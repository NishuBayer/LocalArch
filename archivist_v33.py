from __future__ import annotations

import base64
import csv
import hashlib
import json
import mimetypes
import os
import getpass
import queue
import secrets
import shutil
import sqlite3
import threading
import time
import zipfile
from dataclasses import dataclass
from datetime import datetime
from functools import partial
from hashlib import pbkdf2_hmac
from pathlib import Path
from typing import Iterable

import requests
from requests import RequestException
from PySide6.QtCore import QObject, QPoint, QRect, QSize, QSettings, QThread, Signal, Qt, QTimer, QDateTime, QDate, QTime, QSignalBlocker
from PySide6.QtGui import QColor, QCursor, QPainter, QPainterPath, QPen, QPixmap, QPolygon
from PySide6.QtSvg import QSvgRenderer
from PySide6.QtWidgets import (
    QAbstractItemView,
    QApplication,
    QCheckBox,
    QComboBox,
    QDateTimeEdit,
    QDialog,
    QFileDialog,
    QFormLayout,
    QFrame,
    QGroupBox,
    QHBoxLayout,
    QHeaderView,
    QInputDialog,
    QLabel,
    QLineEdit,
    QListWidget,
    QListWidgetItem,
    QMainWindow,
    QMenu,
    QMessageBox,
    QProgressBar,
    QPushButton,
    QSizePolicy,
    QSpinBox,
    QTableWidget,
    QTableWidgetItem,
    QTabWidget,
    QTextEdit,
    QToolButton,
    QVBoxLayout,
    QWidget,
)


class SvgToggleButton(QWidget):
    """A compact, checkable SVG toggle painted directly, without icon or stylesheet assets.

    The SVG is rendered directly into the widget on every paint.  If an asset is
    not readable or Qt cannot render it, the fallback remains an unambiguous
    checkbox, so selection never becomes visually invisible.
    """

    toggled = Signal(bool)
    clicked = Signal(bool)

    def __init__(
        self,
        checked_path: Path,
        unchecked_path: Path,
        parent: QWidget | None = None,
        *,
        accessible_name: str = "Selection toggle",
        tooltip: str = "Select row",
    ) -> None:
        super().__init__(parent)
        self.checked_path = checked_path
        self.unchecked_path = unchecked_path
        self._checked = False
        self._base_tooltip = tooltip
        self.setFixedSize(18, 18)
        self.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        self.setFocusPolicy(Qt.StrongFocus)
        self.setCursor(Qt.PointingHandCursor)
        self.setToolTip(tooltip)
        self.setAccessibleName(accessible_name)
        self.setAccessibleDescription(tooltip)

    def sizeHint(self) -> QSize:  # noqa: N802
        return QSize(18, 18)

    def minimumSizeHint(self) -> QSize:  # noqa: N802
        return QSize(18, 18)

    def isChecked(self) -> bool:  # noqa: N802
        return self._checked

    def setChecked(self, checked: bool) -> None:  # noqa: N802
        checked = bool(checked)
        if self._checked == checked:
            return
        self._checked = checked
        state = "checked" if checked else "unchecked"
        self.setToolTip(f"{self._base_tooltip} ({state})")
        self.toggled.emit(checked)
        self.update()

    def click(self) -> None:
        """Match checkable-button click ordering: toggle, then announce click."""
        if not self.isEnabled():
            return
        self.setChecked(not self._checked)
        self.clicked.emit(self._checked)

    def mouseReleaseEvent(self, event) -> None:  # noqa: N802
        if event.button() == Qt.LeftButton and self.isEnabled() and self.rect().contains(event.position().toPoint()):
            self.setFocus(Qt.MouseFocusReason)
            self.click()
            event.accept()
            return
        super().mouseReleaseEvent(event)

    def keyPressEvent(self, event) -> None:  # noqa: N802
        if event.key() in (Qt.Key_Space, Qt.Key_Return, Qt.Key_Enter) and self.isEnabled():
            self.click()
            event.accept()
            return
        super().keyPressEvent(event)

    def paintEvent(self, event) -> None:  # noqa: N802
        del event
        painter = QPainter(self)
        painter.setRenderHint(QPainter.Antialiasing)
        target = QRect(0, 0, 18, 18)
        target.moveCenter(self.rect().center())
        asset_path = self.checked_path if self._checked else self.unchecked_path
        rendered = False
        if asset_path.is_file():
            try:
                renderer = QSvgRenderer(str(asset_path))
                if renderer.isValid():
                    renderer.render(painter, target)
                    rendered = True
            except Exception:  # Qt SVG parsing/painting failures use the visible fallback.
                rendered = False
        if not rendered:
            self._paint_fallback(painter, target)
        if self.hasFocus():
            focus_pen = QPen(QColor("#7b61ff"))
            focus_pen.setWidth(1)
            painter.setPen(focus_pen)
            painter.setBrush(Qt.NoBrush)
            painter.drawRoundedRect(self.rect().adjusted(0, 0, -1, -1), 4, 4)
        painter.end()

    def _paint_fallback(self, painter: QPainter, target: QRect) -> None:
        box = target.adjusted(2, 2, -2, -2)
        if self._checked:
            background = QColor("#2f72d6") if self.isEnabled() else QColor("#9eb8d6")
            border = background
        else:
            background = QColor("#ffffff") if self.isEnabled() else QColor("#f1f5f9")
            border = QColor("#94a3b8")
        painter.setPen(QPen(border, 1.25))
        painter.setBrush(background)
        painter.drawRoundedRect(box, 3, 3)
        if self._checked:
            check = QPainterPath()
            check.moveTo(box.left() + 3.0, box.center().y())
            check.lineTo(box.center().x() - 0.5, box.bottom() - 3.5)
            check.lineTo(box.right() - 2.5, box.top() + 3.5)
            pen = QPen(QColor("#ffffff"))
            pen.setWidthF(1.8)
            pen.setCapStyle(Qt.RoundCap)
            pen.setJoinStyle(Qt.RoundJoin)
            painter.setPen(pen)
            painter.setBrush(Qt.NoBrush)
            painter.drawPath(check)


class SvgActionButton(QWidget):
    """Compact action control that paints its sibling SVG without QSS URL loading."""

    clicked = Signal()

    def __init__(
        self,
        asset_name: str,
        *,
        tooltip: str,
        accessible_name: str,
        fallback_text: str,
        parent: QWidget | None = None,
    ) -> None:
        super().__init__(parent)
        self.asset_path = Path(__file__).resolve().parent / asset_name
        self._fallback_text = fallback_text
        self._hovered = False
        self._pressed = False
        self.setFixedSize(20, 20)
        self.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        self.setFocusPolicy(Qt.StrongFocus)
        self.setCursor(Qt.PointingHandCursor)
        self.setToolTip(tooltip)
        self.setAccessibleName(accessible_name)
        self.setAccessibleDescription(tooltip)

    def sizeHint(self) -> QSize:  # noqa: N802
        return QSize(20, 20)

    def minimumSizeHint(self) -> QSize:  # noqa: N802
        return QSize(20, 20)

    def enterEvent(self, event) -> None:  # noqa: N802
        self._hovered = True
        self.update()
        super().enterEvent(event)

    def leaveEvent(self, event) -> None:  # noqa: N802
        self._hovered = False
        self.update()
        super().leaveEvent(event)

    def mousePressEvent(self, event) -> None:  # noqa: N802
        if event.button() == Qt.LeftButton and self.isEnabled():
            self._pressed = True
            self.setFocus(Qt.MouseFocusReason)
            self.update()
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseReleaseEvent(self, event) -> None:  # noqa: N802
        if event.button() == Qt.LeftButton:
            activate = self._pressed and self.isEnabled() and self.rect().contains(event.position().toPoint())
            self._pressed = False
            self.update()
            if activate:
                self.clicked.emit()
            event.accept()
            return
        super().mouseReleaseEvent(event)

    def keyPressEvent(self, event) -> None:  # noqa: N802
        if event.key() in (Qt.Key_Space, Qt.Key_Return, Qt.Key_Enter) and self.isEnabled():
            self.clicked.emit()
            event.accept()
            return
        super().keyPressEvent(event)

    def paintEvent(self, event) -> None:  # noqa: N802
        del event
        painter = QPainter(self)
        painter.setRenderHint(QPainter.Antialiasing)
        if not self.isEnabled():
            background, border = QColor("#f1f5f9"), QColor("#d8dbe3")
        elif self._pressed:
            background, border = QColor("#e1e8f3"), QColor("#9eacc2")
        elif self._hovered:
            background, border = QColor("#f3f6fb"), QColor("#b8c2d9")
        else:
            background, border = QColor("#ffffff"), QColor("#d8dbe3")
        painter.setPen(QPen(border, 1))
        painter.setBrush(background)
        painter.drawRoundedRect(self.rect().adjusted(0, 0, -1, -1), 4, 4)

        target = QRect(3, 3, 14, 14)
        if not render_svg_asset(painter, self.asset_path, target):
            painter.setPen(QColor("#64748b") if self.isEnabled() else QColor("#aab4c2"))
            font = painter.font()
            font.setPixelSize(13)
            font.setBold(True)
            painter.setFont(font)
            painter.drawText(target, Qt.AlignCenter, self._fallback_text)
        if self.hasFocus():
            focus_pen = QPen(QColor("#7b61ff"))
            focus_pen.setWidth(1)
            painter.setPen(focus_pen)
            painter.setBrush(Qt.NoBrush)
            painter.drawRoundedRect(self.rect().adjusted(1, 1, -2, -2), 3, 3)
        painter.end()


class FilterColumnRowLabel(QLabel):
    """A label that makes the descriptive part of a filter row toggleable too."""

    clicked = Signal()

    def mouseReleaseEvent(self, event) -> None:  # noqa: N802
        if event.button() == Qt.LeftButton and self.isEnabled():
            self.clicked.emit()
            event.accept()
            return
        super().mouseReleaseEvent(event)


def render_svg_asset(painter: QPainter, asset_path: Path, target: QRect) -> bool:
    """Render a standalone SVG directly, returning False when no paint is possible."""
    if not asset_path.is_file():
        return False
    try:
        renderer = QSvgRenderer(str(asset_path))
        if not renderer.isValid():
            return False
        renderer.render(painter, target)
        return True
    except Exception:
        return False


class CheckboxHeaderView(QHeaderView):
    """A table header with a centered SVG select-all toggle in one section."""

    def __init__(self, checkbox_column: int, parent: QWidget | None = None) -> None:
        super().__init__(Qt.Horizontal, parent)
        self.checkbox_column = checkbox_column
        asset_dir = Path(__file__).resolve().parent
        self.select_all_checkbox = SvgToggleButton(
            asset_dir / "checked.svg",
            asset_dir / "unchecked.svg",
            self.viewport(),
            accessible_name="Select all history rows",
            tooltip="Select all history rows",
        )
        self.select_all_checkbox.setObjectName("historySelectAllToggle")
        self.sectionResized.connect(self._position_checkbox)
        self.sectionMoved.connect(self._position_checkbox)

    def _position_checkbox(self, *args: object) -> None:
        if self.isSectionHidden(self.checkbox_column):
            self.select_all_checkbox.hide()
            return
        self.select_all_checkbox.show()
        size = self.select_all_checkbox.sizeHint()
        x = self.sectionViewportPosition(self.checkbox_column)
        width = self.sectionSize(self.checkbox_column)
        y = max(0, (self.height() - size.height()) // 2)
        self.select_all_checkbox.setGeometry(
            x + max(0, (width - size.width()) // 2), y, size.width(), size.height()
        )

    def resizeEvent(self, event) -> None:
        super().resizeEvent(event)
        self._position_checkbox()

    def showEvent(self, event) -> None:
        super().showEvent(event)
        self._position_checkbox()


APP_ORG = "Bayer"
APP_NAME = "ArchiveTransferManager"
REQUEST_TIMEOUT = (5, 15)
HASH_READ_SIZE = 8 * 1024 * 1024
STARTABLE_STATUSES = {"Queued"}
MANUALLY_STARTABLE_STATUSES = {"Queued", "Stopped"}
WAITING_FOR_NETWORK_STATUS = "Waiting for Network"
STOPPABLE_STATUSES = {"Ready", "Preparing", "Uploading", WAITING_FOR_NETWORK_STATUS}
CANCELABLE_STATUSES = {"Queued", "Ready", "Preparing", "Uploading", "Stopped", "Failed", WAITING_FOR_NETWORK_STATUS}
RETRYABLE_STATUSES = {"Failed"}
IN_PROGRESS_STATUSES = {"Ready", "Preparing", "Uploading"}
DB_FILE_NAME = "archive_history.db"
SUPPORT_LOG_PASSWORD = "Admin@321"
CONFIG_ENCRYPTION_PASSWORD = "Config@Admin123"
CONFIG_PBKDF2_ITERATIONS = 390000
WINDOWS_USER_METADATA_COLUMN = "Archive Uploader"
QUERY_OPERATOR_OPTIONS = ["contains", "equals", "starts with", "ends with"]
QUERY_FIELD_OPTIONS = [
    "Run ID",
    "File Name",
    "Full Path",
    "Size",
    "File Hash",
    "Task ID",
    "Status",
    "Archival Timestamp",
    "Archive Metadata",
]
HISTORY_STATUS_ORDER = [
    "Queued",
    "Ready",
    "Preparing",
    "Uploading",
    "Completed",
    "Stopped",
    "Canceled",
    "Failed",
]


def app_storage_dir() -> Path:
    local_appdata = os.getenv("LOCALAPPDATA")
    appdata = os.getenv("APPDATA")
    base_dir = Path(local_appdata or appdata or Path.home())
    storage_dir = base_dir / "LocalArchivist"
    storage_dir.mkdir(parents=True, exist_ok=True)
    return storage_dir


def db_file_path() -> Path:
    return app_storage_dir() / DB_FILE_NAME


def logs_dir_path() -> Path:
    path = app_storage_dir() / "archive_logs"
    path.mkdir(parents=True, exist_ok=True)
    return path


@dataclass(slots=True)
class ArchiveConfig:
    """Configuration required to archive files."""

    auth_server_url: str
    archive_service_url: str
    client_app_id: str
    client_secret: str
    archive_service_app_id: str
    proxy_url: str
    proxy_enabled: bool
    chunk_size_mb: int
    retry_count: int
    data_owner: str
    country: str
    data_classification: str
    retention_policy: str
    required_retrieval_time: str


@dataclass(slots=True)
class ArchiveTask:
    """Represents one file archiving task shown in the table."""

    row: int
    file_path: Path
    relative_path: str
    size_bytes: int
    full_path: str = ""
    file_name: str = ""
    file_hash: str = "-"
    archived_at: str = "-"
    status: str = "Queued"
    progress: int = 0
    task_id: str = "-"
    stop_requested: bool = False
    cancel_requested: bool = False
    custom_business_metadata: dict[str, str] | None = None
    is_transfer_zip: bool = False
    zip_source_files: tuple[Path, ...] = ()
    zip_source_root: Path | None = None
    # Durable recovery fields recorded using documented archive-service contracts.
    commit_state: str = "not_requested"
    source_size: int = 0
    source_mtime: float = 0.0
    # Exact JSON payload submitted to the documented create-upload endpoint.
    metadata_json: str = "{}"


class ArchiveError(Exception):
    """Raised when archiving a file fails."""


class TaskStoppedError(Exception):
    """Raised when a running task is stopped by the user."""


class TaskCanceledError(Exception):
    """Raised when a running task is canceled by the user."""


class NetworkUnavailableError(ArchiveError):
    """Raised when a request cannot continue because connectivity was lost."""


class ArchiveHistoryDatabase:
    """SQLite persistence for local recovery checkpoints.

    The archive API has no idempotency-key contract and no list-parts endpoint.
    Part acknowledgements are therefore deliberately local state.
    """

    def __init__(self, db_path: Path) -> None:
        self.db_path = db_path
        self._lock = threading.RLock()
        self.connection = sqlite3.connect(str(db_path), check_same_thread=False)
        self.connection.row_factory = sqlite3.Row
        self._initialize()

    def _execute(self, statement: str, params: tuple = ()) -> sqlite3.Cursor:
        with self._lock:
            cursor = self.connection.execute(statement, params)
            self.connection.commit()
            return cursor

    def _initialize(self) -> None:
        with self._lock:
            self.connection.execute("PRAGMA journal_mode=WAL")
            self.connection.execute("""CREATE TABLE IF NOT EXISTS archive_runs (
                id INTEGER PRIMARY KEY AUTOINCREMENT, root_folder TEXT NOT NULL, started_at TEXT NOT NULL,
                last_updated TEXT NOT NULL, total_files INTEGER NOT NULL, total_bytes INTEGER NOT NULL,
                completed_count INTEGER NOT NULL DEFAULT 0, failed_count INTEGER NOT NULL DEFAULT 0,
                in_progress_count INTEGER NOT NULL DEFAULT 0, pending_count INTEGER NOT NULL DEFAULT 0,
                canceled_count INTEGER NOT NULL DEFAULT 0)""")
            self.connection.execute("""CREATE TABLE IF NOT EXISTS archive_tasks (
                id INTEGER PRIMARY KEY AUTOINCREMENT, run_id INTEGER NOT NULL, row_index INTEGER NOT NULL,
                relative_path TEXT NOT NULL, full_path TEXT NOT NULL DEFAULT '', file_name TEXT NOT NULL DEFAULT '',
                file_hash TEXT NOT NULL DEFAULT '-', archived_at TEXT NOT NULL DEFAULT '-', size_bytes INTEGER NOT NULL,
                task_id TEXT NOT NULL, progress INTEGER NOT NULL, status TEXT NOT NULL, updated_at TEXT NOT NULL,
                commit_state TEXT NOT NULL DEFAULT 'not_requested', source_size INTEGER NOT NULL DEFAULT 0,
                source_mtime REAL NOT NULL DEFAULT 0, metadata_json TEXT NOT NULL DEFAULT '{}',
                FOREIGN KEY(run_id) REFERENCES archive_runs(id),
                UNIQUE(run_id, row_index))""")
            self.connection.execute("""CREATE TABLE IF NOT EXISTS archive_task_parts (
                run_id INTEGER NOT NULL, row_index INTEGER NOT NULL, part_number INTEGER NOT NULL,
                part_hash TEXT NOT NULL, status TEXT NOT NULL, updated_at TEXT NOT NULL,
                PRIMARY KEY(run_id, row_index, part_number),
                FOREIGN KEY(run_id) REFERENCES archive_runs(id))""")
            existing = {str(row[1]) for row in self.connection.execute("PRAGMA table_info(archive_tasks)").fetchall()}
            migrations = {
                "full_path": "ALTER TABLE archive_tasks ADD COLUMN full_path TEXT NOT NULL DEFAULT ''",
                "file_name": "ALTER TABLE archive_tasks ADD COLUMN file_name TEXT NOT NULL DEFAULT ''",
                "file_hash": "ALTER TABLE archive_tasks ADD COLUMN file_hash TEXT NOT NULL DEFAULT '-'",
                "archived_at": "ALTER TABLE archive_tasks ADD COLUMN archived_at TEXT NOT NULL DEFAULT '-'",
                "commit_state": "ALTER TABLE archive_tasks ADD COLUMN commit_state TEXT NOT NULL DEFAULT 'not_requested'",
                "source_size": "ALTER TABLE archive_tasks ADD COLUMN source_size INTEGER NOT NULL DEFAULT 0",
                "source_mtime": "ALTER TABLE archive_tasks ADD COLUMN source_mtime REAL NOT NULL DEFAULT 0",
                "metadata_json": "ALTER TABLE archive_tasks ADD COLUMN metadata_json TEXT NOT NULL DEFAULT '{}'",
            }
            for column, statement in migrations.items():
                if column not in existing:
                    self.connection.execute(statement)
            self.connection.commit()

    def create_run(self, root_folder: str, task_snapshots: list[dict[str, object]]) -> int:
        now = current_timestamp(); counts = calculate_status_counts(task_snapshots)
        cursor = self._execute("""INSERT INTO archive_runs (root_folder,started_at,last_updated,total_files,total_bytes,completed_count,failed_count,in_progress_count,pending_count,canceled_count) VALUES (?,?,?,?,?,?,?,?,?,?)""", (root_folder,now,now,len(task_snapshots),sum(int(x['size_bytes']) for x in task_snapshots),counts['completed'],counts['failed'],counts['in_progress'],counts['pending'],counts['canceled']))
        return int(cursor.lastrowid)

    def upsert_task(self, run_id: int, x: dict[str, object]) -> None:
        columns = "run_id,row_index,relative_path,full_path,file_name,file_hash,archived_at,size_bytes,task_id,progress,status,updated_at,commit_state,source_size,source_mtime,metadata_json"
        values = (run_id,int(x['row_index']),str(x['relative_path']),str(x.get('full_path','')),str(x.get('file_name','')),str(x.get('file_hash','-')),str(x.get('archived_at','-')),int(x['size_bytes']),str(x['task_id']),int(x['progress']),str(x['status']),str(x['updated_at']),str(x.get('commit_state','not_requested')),int(x.get('source_size',0)),float(x.get('source_mtime',0)),str(x.get('metadata_json','{}') or '{}'))
        updates = ','.join(f"{c}=excluded.{c}" for c in columns.split(',')[2:])
        self._execute(f"INSERT INTO archive_tasks ({columns}) VALUES ({','.join('?' for _ in values)}) ON CONFLICT(run_id,row_index) DO UPDATE SET {updates}", values)

    def persist_part_state(self, run_id: int, row: int, part_number: int, part_hash: str, status: str) -> None:
        self._execute("""INSERT INTO archive_task_parts(run_id,row_index,part_number,part_hash,status,updated_at) VALUES(?,?,?,?,?,?) ON CONFLICT(run_id,row_index,part_number) DO UPDATE SET part_hash=excluded.part_hash,status=excluded.status,updated_at=excluded.updated_at""", (run_id,row,part_number,part_hash,status,current_timestamp()))

    def fetch_part_states(self, run_id: int, row: int) -> dict[int, tuple[str, str]]:
        with self._lock:
            rows = self.connection.execute("SELECT part_number,part_hash,status FROM archive_task_parts WHERE run_id=? AND row_index=?", (run_id,row)).fetchall()
        return {int(item['part_number']): (str(item['part_hash']), str(item['status'])) for item in rows}

    def update_run_summary(self, run_id: int, snapshots: list[dict[str, object]]) -> None:
        c=calculate_status_counts(snapshots)
        self._execute("""UPDATE archive_runs SET last_updated=?,total_files=?,total_bytes=?,completed_count=?,failed_count=?,in_progress_count=?,pending_count=?,canceled_count=? WHERE id=?""",(current_timestamp(),len(snapshots),sum(int(x['size_bytes']) for x in snapshots),c['completed'],c['failed'],c['in_progress'],c['pending'],c['canceled'],run_id))

    def fetch_runs(self, limit: int=100) -> list[sqlite3.Row]:
        with self._lock: return self.connection.execute("SELECT * FROM archive_runs ORDER BY id DESC LIMIT ?",(limit,)).fetchall()
    def fetch_task_history(self, limit: int=500) -> list[sqlite3.Row]:
        with self._lock: return self.connection.execute("SELECT t.run_id,t.row_index,t.relative_path,t.full_path,t.file_name,t.file_hash,t.archived_at,t.size_bytes,t.task_id,t.progress,t.status,t.updated_at,t.metadata_json FROM archive_tasks t ORDER BY t.updated_at DESC,t.run_id DESC,t.row_index ASC LIMIT ?",(limit,)).fetchall()
    def close(self) -> None:
        with self._lock: self.connection.close()


class Worker(QObject):
    update_row = Signal(int, int, str)
    update_task_id = Signal(int, str)
    overall_progress = Signal(int)
    log = Signal(str)
    finished = Signal()

    def __init__(
        self,
        tasks: list[ArchiveTask],
        root_folder: Path,
        config: ArchiveConfig,
        task_lock: threading.Lock,
        history_db: ArchiveHistoryDatabase,
        run_id: int,
    ) -> None:
        super().__init__()
        self.tasks = tasks
        self.root_folder = root_folder
        self.config = config
        self.task_lock = task_lock
        # The database serializes access; this worker uses it for crash-safe checkpoints.
        self.history_db = history_db
        self.run_id = run_id

    def run(self) -> None:
        try:
            if not self.tasks:
                self.log.emit("No files found to archive.")
                self.overall_progress.emit(0)
                return

            session = self._build_session()
            self._technical_log(
                "worker_started",
                run_id=self.run_id,
                root_folder=str(self.root_folder),
                task_count=len(self.tasks),
                chunk_size_mb=self.config.chunk_size_mb,
                retry_count=self.config.retry_count,
                proxy_enabled=self.config.proxy_enabled,
                proxy_configured=bool(self.config.proxy_url.strip()),
                archive_service_url=self.config.archive_service_url,
                auth_server_url=self.config.auth_server_url,
            )
            token = self._get_access_token(session)
            auth_header = {"Authorization": f"Bearer {token}"}
            self._technical_log("authentication_succeeded", run_id=self.run_id, token_received=True)

            while True:
                task = self._next_ready_task()
                if task is None:
                    break

                try:
                    self._set_task_status(task, "Preparing", progress=0)
                    self._technical_log(
                        "task_started",
                        run_id=self.run_id,
                        row_index=task.row,
                        relative_path=task.relative_path,
                        full_path=str(task.file_path),
                        size_bytes=task.size_bytes,
                        existing_task_id=task.task_id,
                    )
                    self.log.emit(f"Starting: {task.relative_path}")
                    task_id, archived_at = self._archive_file(session=session, task=task, auth_header=auth_header)
                    self._set_task_status(task, "Completed", progress=100, task_id=task_id, archived_at=archived_at)
                    self._technical_log("task_completed", run_id=self.run_id, row_index=task.row, relative_path=task.relative_path, task_id=task_id, archived_at=archived_at)
                    self.log.emit(f"Completed: {task.relative_path} | task-id: {task_id}")
                except TaskStoppedError:
                    self._set_task_status(task, "Stopped")
                    self.log.emit(
                        f"Stopped: {task.relative_path} | task-id: {task.task_id}. "
                        "Upload was stopped locally before commit."
                    )
                except TaskCanceledError:
                    self._set_task_status(task, "Canceled")
                    self.log.emit(
                        f"Canceled: {task.relative_path} | task-id: {task.task_id}. "
                        "Upload was canceled locally before commit."
                    )
                except NetworkUnavailableError:
                    self._set_task_status(task, WAITING_FOR_NETWORK_STATUS)
                    self.log.emit(f"Network unavailable: {task.relative_path} is waiting to resume.")
                except Exception as exc:  # noqa: BLE001
                    self._set_task_status(task, "Failed")
                    self._technical_log(
                        "task_failed",
                        run_id=self.run_id,
                        row_index=task.row,
                        relative_path=task.relative_path,
                        task_id=task.task_id,
                        error_type=type(exc).__name__,
                        error=str(exc),
                    )
                    self.log.emit(f"Failed: {task.relative_path} | {exc}")

            self._emit_overall_progress()
            self._technical_log("worker_finished", run_id=self.run_id)
        finally:
            self.finished.emit()

    def _technical_log(self, event: str, **details: object) -> None:
        """Emit a structured technical event without exposing credentials or tokens."""
        safe_details = {
            key: value
            for key, value in details.items()
            if key.casefold() not in {"token", "access_token", "authorization", "password", "secret", "client_secret"}
        }
        serialized = json.dumps(safe_details, ensure_ascii=False, default=str, separators=(",", ":"))
        self.log.emit(f"TECHNICAL | {event} | {serialized}")

    def _build_session(self) -> requests.Session:
        session = requests.Session()
        session.trust_env = False
        proxy_url = self.config.proxy_url.strip()
        if self.config.proxy_enabled and proxy_url:
            session.proxies.update({"http": proxy_url, "https": proxy_url})
        return session

    def _get_access_token(self, session: requests.Session) -> str:
        scope = f"https://bayergroup.onmicrosoft.com/{self.config.archive_service_app_id}/.default"
        payload = {"grant_type": "client_credentials", "scope": scope}
        self._technical_log("authentication_requested", method="POST", url=self.config.auth_server_url, scope=scope)
        response = self._request_with_retries(
            session=session,
            method="post",
            url=self.config.auth_server_url,
            data=payload,
            allow_redirects=False,
            auth=(self.config.client_app_id, self.config.client_secret),
        )
        token = response.json().get("access_token")
        if not token:
            raise ArchiveError("Authentication succeeded but access token was missing.")
        return token

    def _archive_file(
        self, *, session: requests.Session, task: ArchiveTask, auth_header: dict[str, str]
    ) -> tuple[str, str]:
        """Archive or recover a file using only the documented API operations.

        Local part state is authoritative only for deciding what this client has
        checkpointed.  The service does not provide a list-parts operation, so an
        ``uploaded`` checkpoint is never re-uploaded; a PUT that succeeded just
        before its checkpoint is instead represented by ``upload_requested`` and
        is safely re-PUT after refreshing its documented part URL.
        """
        self._check_control_flags(task)
        stat = task.file_path.stat()
        file_size, file_hash = get_file_properties(task.file_path)
        self._technical_log(
            "source_file_inspected",
            run_id=self.run_id,
            row_index=task.row,
            relative_path=task.relative_path,
            file_size=file_size,
            file_hash=file_hash,
            source_mtime=stat.st_mtime,
            mime_type=get_mime_type(task.file_path),
        )
        with self.task_lock:
            if task.source_size and (task.source_size != file_size or task.source_mtime != stat.st_mtime):
                raise ArchiveError("Source changed since the resumable upload was created; refusing unsafe resume.")
            task.source_size, task.source_mtime = file_size, stat.st_mtime
        self._set_task_status(task, task.status, file_hash=file_hash)
        self._persist_task_checkpoint(task)

        metadata = {
            "file-metadata": {"hash": file_hash, "filesize": file_size, "filename": task.file_path.name, "mime-type": get_mime_type(task.file_path)},
            "business-metadata": {"source-relative-path": str(Path(task.relative_path).parent).replace(".", "").strip("/\\") or "/", "source-filename": task.file_path.name, "source-full-relative-path": task.relative_path, "source-root-relative-full-path": f"{self.root_folder}\\{task.relative_path.replace('/', '\\')}", **{k:v for k,v in (task.custom_business_metadata or {}).items() if k.strip() and v.strip()}},
            "archiving-metadata": {"data-classification": self.config.data_classification, "retention-policy": self.config.retention_policy, "required-retrieval-time": self.config.required_retrieval_time, "gxp": False, "ics": False, "country": self.config.country, "data-owner": self.config.data_owner},
        }
        # Checkpoint the exact create-upload payload before making the request.
        # A resumed task retains its original create payload even if settings later change.
        metadata_json = json.dumps(metadata, ensure_ascii=False, separators=(",", ":"))
        self._technical_log(
            "metadata_prepared",
            run_id=self.run_id,
            row_index=task.row,
            relative_path=task.relative_path,
            business_metadata_keys=sorted((task.custom_business_metadata or {}).keys()),
            metadata_json=metadata_json,
        )
        with self.task_lock:
            creating_upload = task.task_id in {"", "-"}
            if creating_upload:
                task.metadata_json = metadata_json
        if creating_upload:
            self._persist_task_checkpoint(task)

        task_id = task.task_id
        if task_id not in {"", "-"}:
            payload = self._remote_status_payload(session, task_id, auth_header)
            status = self._require_recoverable_status(task_id, payload)
            if status in {"verified", "archived"}:
                self.log.emit(f"Remote task {task_id} is {status}; completing local task without another commit.")
                return task_id, current_date_string()
            if status == "indexing":
                self._wait_for_completion(session, task_id, auth_header)
                return task_id, current_date_string()
            self.log.emit(f"Resuming active remote task {task_id} in status {status}.")
        else:
            # No API idempotency key is documented. Do not retry an uncertain create.
            self._technical_log("create_upload_requested", run_id=self.run_id, row_index=task.row, method="POST", url=self._service_url("/v1/create-upload"), metadata_json=metadata_json)
            response = self._request_once(session, "post", self._service_url("/v1/create-upload"), json=metadata, headers=auth_header)
            create_response = self._safe_json_response(response)
            task_id = str(create_response.get("task-id") or "")
            self._technical_log("create_upload_response", run_id=self.run_id, row_index=task.row, status_code=response.status_code, task_id=task_id, response=create_response)
            if not task_id:
                raise ArchiveError("Archive service did not return a task-id.")
            self._set_task_status(task, task.status, task_id=task_id)
            self._persist_task_checkpoint(task)

        chunk_size = max(1, self.config.chunk_size_mb) * 1024 * 1024
        total_chunks = max(1, (file_size + chunk_size - 1) // chunk_size)
        self._technical_log("upload_plan", run_id=self.run_id, row_index=task.row, task_id=task_id, chunk_size_bytes=chunk_size, total_chunks=total_chunks, file_size=file_size)
        part_states = self.history_db.fetch_part_states(self.run_id, task.row)
        loaded_size = 0
        self._set_task_status(task, "Uploading", progress=0)
        with task.file_path.open("rb") as handle:
            for expected_number in range(1, total_chunks + 1):
                self._check_control_flags(task)
                chunk = handle.read(chunk_size)
                part_hash = get_sha256_hash(chunk)
                recorded = part_states.get(expected_number)
                if recorded is not None and recorded[0] != part_hash:
                    raise ArchiveError(f"Persisted hash for part {expected_number} does not match the source file.")
                if recorded is not None and recorded[1] == "uploaded":
                    # No list-parts endpoint exists; this is intentionally local-state based.
                    self.log.emit(f"Locally checkpointed part {expected_number}; not re-uploading it.")
                else:
                    if recorded is not None:
                        # Persist intent before refreshing. Same number/hash refreshes a documented part URL.
                        self.history_db.persist_part_state(self.run_id, task.row, expected_number, part_hash, "upload_requested")
                        part_request = {"task-id": task_id, "part-hash": part_hash, "part-number": expected_number}
                    else:
                        # New parts omit part-number. If we crash before the response, the next run again
                        # calculates this sequential position and does not claim an unpersisted number.
                        part_request = {"task-id": task_id, "part-hash": part_hash}
                    self._technical_log("create_upload_part_requested", run_id=self.run_id, row_index=task.row, task_id=task_id, part_number=expected_number, part_hash=part_hash, request=part_request)
                    create = self._request_once(session, "post", self._service_url("/v1/create-upload-part"), json=part_request, headers=auth_header)
                    created = self._safe_json_response(create)
                    self._technical_log("create_upload_part_response", run_id=self.run_id, row_index=task.row, task_id=task_id, expected_part_number=expected_number, status_code=create.status_code, response=created)
                    returned_number = created.get("part-number")
                    data_url = created.get("data-url")
                    if not isinstance(returned_number, int) or not data_url:
                        raise ArchiveError(f"Missing part-number or data-url for source part {expected_number}.")
                    if recorded is not None and returned_number != expected_number:
                        raise ArchiveError(f"Refresh returned part-number {returned_number}, expected {expected_number}.")
                    if recorded is None and returned_number != expected_number:
                        raise ArchiveError(f"New part returned {returned_number}, expected sequential part {expected_number}; refusing unsafe ordering.")
                    self.history_db.persist_part_state(self.run_id, task.row, returned_number, part_hash, "upload_requested")
                    # The documented presigned PUT requires only this checksum header.
                    self._technical_log("part_upload_requested", run_id=self.run_id, row_index=task.row, task_id=task_id, part_number=returned_number, part_hash=part_hash, bytes=len(chunk), url_host=str(data_url).split("/")[2] if "://" in str(data_url) else "")
                    put_response = self._request_with_retries(session=session, method="put", url=str(data_url), headers={"x-amz-checksum-sha256": part_hash}, data=chunk)
                    self._technical_log("part_upload_response", run_id=self.run_id, row_index=task.row, task_id=task_id, part_number=returned_number, status_code=put_response.status_code)
                    self.history_db.persist_part_state(self.run_id, task.row, returned_number, part_hash, "uploaded")
                    part_states[returned_number] = (part_hash, "uploaded")
                loaded_size += len(chunk)
                self._set_task_status(task, "Uploading", progress=self._safe_percentage(expected_number, total_chunks))
                self._emit_overall_progress(task.row, loaded_size)

        self._check_control_flags(task)
        # If a prior commit request is uncertain, status is always checked before POST /commit.
        if task.commit_state == "commit_requested":
            payload = self._remote_status_payload(session, task_id, auth_header)
            status = self._require_recoverable_status(task_id, payload)
            if status in {"verified", "archived"}:
                return task_id, current_date_string()
            if status == "indexing":
                self._wait_for_completion(session, task_id, auth_header)
                return task_id, current_date_string()
        with self.task_lock:
            task.commit_state = "commit_requested"
        self._persist_task_checkpoint(task)
        try:
            self._technical_log("commit_requested", run_id=self.run_id, row_index=task.row, task_id=task_id, method="POST", url=self._service_url("/v1/commit"))
            commit_response = self._request_once(session, "post", self._service_url("/v1/commit"), json={"task-id": task_id}, headers=auth_header)
            self._technical_log("commit_response", run_id=self.run_id, row_index=task.row, task_id=task_id, status_code=commit_response.status_code)
        except ArchiveError:
            payload = self._remote_status_payload(session, task_id, auth_header)
            status = self._require_recoverable_status(task_id, payload)
            if status not in {"verified", "archived", "indexing"}:
                # Status was checked first; one documented commit retry is now appropriate.
                self._request_once(session, "post", self._service_url("/v1/commit"), json={"task-id": task_id}, headers=auth_header)
        self._wait_for_completion(session, task_id, auth_header)
        with self.task_lock:
            task.commit_state = "completed"
        self._persist_task_checkpoint(task)
        return task_id, current_date_string()

    def _remote_status_payload(self, session: requests.Session, task_id: str, auth_header: dict[str, str]) -> dict[str, object]:
        response = self._request_with_retries(session=session, method="get", url=self._service_url("/v1/status"), params={"task-id": task_id}, headers=auth_header)
        payload = self._safe_json_response(response)
        self._technical_log("remote_status_response", run_id=self.run_id, task_id=task_id, status_code=response.status_code, response=payload)
        return payload

    def _require_recoverable_status(self, task_id: str, payload: dict[str, object]) -> str:
        status = str(payload.get("status", "")).lower()
        detail = str(payload.get("detailed-message", "")).strip()
        if status in {"aborted", "verification-failed", "indexing-failed"}:
            message = f"Remote task {task_id} is {status}."
            if detail:
                message += f" Detailed message: {detail}"
            self.log.emit(message)
            raise ArchiveError(message + " This task will not be reused.")
        if status not in {"created", "in-progress", "indexing", "verified", "archived"}:
            raise ArchiveError(f"Remote task {task_id} returned unsupported or missing status {status!r}.")
        return status

    def _wait_for_completion(self, session: requests.Session, task_id: str, auth_header: dict[str, str]) -> None:
        for attempt in range(1, self.config.retry_count + 1):
            status = self._require_recoverable_status(task_id, self._remote_status_payload(session, task_id, auth_header))
            if status in {"verified", "archived"}:
                return
            self.log.emit(f"Remote task {task_id} remains {status}; waiting for verification ({attempt}/{self.config.retry_count}).")
            if attempt < self.config.retry_count:
                self._interruptible_wait(task_id, task=None, seconds=min(2 * attempt, 10))
        raise ArchiveError(f"Remote task {task_id} did not reach verified or archived status after commit.")

    def _interruptible_wait(self, task_id: str, task: ArchiveTask | None, seconds: float) -> None:
        """Poll control flags during retry/poll waits instead of blocking stop/cancel."""
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            if task is not None:
                self._check_control_flags(task)
            time.sleep(min(0.1, max(0.0, deadline - time.monotonic())))

    def _request_once(self, session: requests.Session, method: str, url: str, **kwargs) -> requests.Response:
        try:
            response = session.request(method=method, url=url, timeout=REQUEST_TIMEOUT, **kwargs)
            self._technical_log("http_response", method=method.upper(), url=url, status_code=response.status_code)
            response.raise_for_status()
            return response
        except requests.RequestException as exc:
            response = getattr(exc, "response", None)
            self._technical_log("http_request_failed", method=method.upper(), url=url, status_code=getattr(response, "status_code", None), error_type=type(exc).__name__, error=str(exc))
            raise ArchiveError(str(exc)) from exc

    def _has_network_connectivity(self, session: requests.Session) -> bool:
        url = self.config.archive_service_url.strip() or self.config.auth_server_url.strip()
        if not url:
            return False
        try:
            response = session.get(url, timeout=5, allow_redirects=False)
            return response.status_code < 500
        except requests.RequestException:
            return False

    def _move_ready_tasks_to_waiting_for_network(self) -> None:
        waiting_tasks: list[ArchiveTask] = []
        with self.task_lock:
            for task in self.tasks:
                if task.status == "Ready":
                    task.status = WAITING_FOR_NETWORK_STATUS
                    waiting_tasks.append(task)
        for task in waiting_tasks:
            self.update_row.emit(task.row, task.progress, WAITING_FOR_NETWORK_STATUS)
        if waiting_tasks:
            self.log.emit("Network became unavailable. Remaining archive tasks are waiting for network connectivity.")

    def _next_ready_task(self) -> ArchiveTask | None:
        with self.task_lock:
            for task in self.tasks:
                if task.status == "Ready":
                    task.stop_requested = False
                    task.cancel_requested = False
                    return task
        return None

    def _set_task_status(
        self,
        task: ArchiveTask,
        status: str,
        *,
        progress: int | None = None,
        task_id: str | None = None,
        file_hash: str | None = None,
        archived_at: str | None = None,
    ) -> None:
        with self.task_lock:
            task.status = status
            if progress is not None:
                task.progress = progress
            if task_id is not None:
                task.task_id = task_id
            if file_hash is not None:
                task.file_hash = file_hash
            if archived_at is not None:
                task.archived_at = archived_at
            current_progress = task.progress
            current_task_id = task.task_id

        self.update_row.emit(task.row, current_progress, status)
        self.update_task_id.emit(task.row, current_task_id)

    def _persist_task_checkpoint(self, task: ArchiveTask) -> None:
        """Synchronously durable worker checkpoint; do not rely on queued UI signals."""
        with self.task_lock:
            snapshot = {
                "row_index": task.row, "relative_path": task.relative_path,
                "full_path": task.full_path or str(task.file_path),
                "file_name": task.file_name or task.file_path.name, "file_hash": task.file_hash,
                "archived_at": task.archived_at, "size_bytes": task.size_bytes,
                "task_id": task.task_id, "progress": task.progress, "status": task.status,
                "commit_state": task.commit_state, "source_size": task.source_size,
                "source_mtime": task.source_mtime, "metadata_json": task.metadata_json,
                "updated_at": current_timestamp(),
            }
        self.history_db.upsert_task(self.run_id, snapshot)

    def _check_control_flags(self, task: ArchiveTask) -> None:
        with self.task_lock:
            stop_requested = task.stop_requested
            cancel_requested = task.cancel_requested
        if cancel_requested:
            raise TaskCanceledError(task.relative_path)
        if stop_requested:
            raise TaskStoppedError(task.relative_path)

    def _emit_overall_progress(self, active_row: int | None = None, active_loaded: int = 0) -> None:
        with self.task_lock:
            total_bytes = sum(task.size_bytes for task in self.tasks if task.status != "Canceled")
            completed_bytes = sum(task.size_bytes for task in self.tasks if task.status == "Completed")
            if active_row is not None:
                completed_bytes += active_loaded
        self.overall_progress.emit(self._safe_percentage(completed_bytes, total_bytes))

    def _request_with_retries(self, session: requests.Session, method: str, url: str, **kwargs) -> requests.Response:
        last_error: Exception | None = None
        for attempt in range(1, self.config.retry_count + 1):
            try:
                response = session.request(method=method, url=url, timeout=REQUEST_TIMEOUT, **kwargs)
                self._technical_log("http_response", method=method.upper(), url=url, attempt=attempt, status_code=response.status_code)
                response.raise_for_status()
                return response
            except requests.RequestException as exc:
                last_error = exc
                response = getattr(exc, "response", None)
                self._technical_log("http_request_retry", method=method.upper(), url=url, attempt=attempt, max_attempts=self.config.retry_count, status_code=getattr(response, "status_code", None), error_type=type(exc).__name__, error=str(exc))
                self.log.emit(f"Request attempt {attempt}/{self.config.retry_count} failed for {url}: {exc}")
                if attempt < self.config.retry_count:
                    # Keep retry delays short and responsive; a control action is
                    # observed as soon as the current request returns.
                    time.sleep(min(2 * attempt, 2))
        if not self._has_network_connectivity(session):
            raise NetworkUnavailableError(f"Network unavailable while requesting {url}")
        raise ArchiveError(str(last_error) if last_error else f"Request failed for {url}")

    @staticmethod
    def _safe_json_response(response: requests.Response) -> dict[str, object]:
        try:
            payload = response.json()
            if isinstance(payload, dict):
                return payload
            return {"response": payload}
        except ValueError:
            text = response.text.strip()
            return {"raw_text": text if text else "<empty response body>"}

    @staticmethod
    def _safe_percentage(current: int, total: int) -> int:
        if total <= 0:
            return 0
        return int((current / total) * 100)

    def _service_url(self, suffix: str) -> str:
        return f"{self.config.archive_service_url.rstrip('/')}{suffix}"


def get_sha256_hash(file_bytes: bytes) -> str:
    digest = hashlib.sha256(file_bytes).digest()
    return base64.b64encode(digest).decode("utf-8")


def get_mime_type(path: Path) -> str:
    mime_type, _ = mimetypes.guess_type(str(path))
    return mime_type or "application/octet-stream"


def get_file_properties(path: Path) -> tuple[int, str]:
    sha256 = hashlib.sha256()
    with path.open("rb") as handle:
        while True:
            chunk = handle.read(HASH_READ_SIZE)
            if not chunk:
                break
            sha256.update(chunk)
    digest = sha256.digest()
    return path.stat().st_size, base64.b64encode(digest).decode("utf-8")


def iter_files_recursively(folder: Path) -> Iterable[Path]:
    excluded_folder_names = {"Outbound", "Zip Outbound", "Cancelled", "cancelled"}
    for path in sorted(folder.rglob("*")):
        if any(part in excluded_folder_names for part in path.parts):
            continue
        if path.is_file():
            yield path


def current_timestamp() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def current_date_string() -> str:
    return datetime.now().strftime("%Y-%m-%d")


def calculate_status_counts(task_snapshots: list[dict[str, object]]) -> dict[str, int]:
    statuses = [str(snapshot["status"]) for snapshot in task_snapshots]
    return {
        "total": len(statuses),
        "completed": sum(status == "Completed" for status in statuses),
        "failed": sum(status == "Failed" for status in statuses),
        "in_progress": sum(status in IN_PROGRESS_STATUSES for status in statuses),
        "pending": sum(status in {"Queued", "Stopped", WAITING_FOR_NETWORK_STATUS} for status in statuses),
        "canceled": sum(status == "Canceled" for status in statuses),
    }


def aggregate_run_history(runs: list[sqlite3.Row]) -> dict[str, int]:
    total_runs = len(runs)
    total_files = sum(int(run["total_files"]) for run in runs)
    total_bytes = sum(int(run["total_bytes"]) for run in runs)
    completed = sum(int(run["completed_count"]) for run in runs)
    failed = sum(int(run["failed_count"]) for run in runs)
    in_progress = sum(int(run["in_progress_count"]) for run in runs)
    pending = sum(int(run["pending_count"]) for run in runs)
    canceled = sum(int(run["canceled_count"]) for run in runs)
    return {
        "runs": total_runs,
        "files": total_files,
        "total_bytes": total_bytes,
        "completed": completed,
        "failed": failed,
        "in_progress": in_progress,
        "pending": pending,
        "canceled": canceled,
    }


def format_size(size_bytes: int) -> str:
    value = float(size_bytes)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if value < 1024 or unit == "TB":
            if unit == "B":
                return f"{int(value)} {unit}"
            return f"{value:.2f} {unit}"
        value /= 1024
    return f"{size_bytes} B"


class CalendarPopupDateEdit(QDateTimeEdit):
    def mousePressEvent(self, event) -> None:  # noqa: N802
        super().mousePressEvent(event)
        calendar = self.calendarWidget()
        if calendar is not None:
            calendar.show()

    def focusInEvent(self, event) -> None:  # noqa: N802
        super().focusInEvent(event)

        def _show_calendar() -> None:
            calendar = self.calendarWidget()
            if calendar is not None:
                calendar.show()

        QTimer.singleShot(0, _show_calendar)


class MetadataHeader(QHeaderView):
    """Header that provides replicate and remove actions for custom metadata columns."""

    def __init__(self, table: QTableWidget, parent: QWidget | None = None) -> None:
        super().__init__(Qt.Horizontal, parent)
        self.table = table
        self.setSectionsClickable(True)

    def paintSection(self, painter: QPainter, rect: QRect, logical_index: int) -> None:  # noqa: N802
        super().paintSection(painter, rect, logical_index)
        owner = self.window()
        if not isinstance(owner, MainWindow):
            return
        metadata_start = 4
        metadata_end = metadata_start + len(owner.custom_business_metadata_columns)
        if not (metadata_start <= logical_index < metadata_end):
            return
        icon_size = 14
        if owner.archive_source_mode.currentData() == "folder":
            replicate_path = Path(__file__).resolve().parent / "replicate.svg"
            render_svg_asset(
                painter,
                replicate_path,
                QRect(rect.left() + 5, rect.center().y() - icon_size // 2, icon_size, icon_size),
            )
        column_name = owner.custom_business_metadata_columns[logical_index - metadata_start]
        if owner.is_manual_business_metadata_column(column_name):
            remove_path = Path(__file__).resolve().parent / "remove.svg"
            render_svg_asset(
                painter,
                remove_path,
                QRect(rect.right() - icon_size - 5, rect.center().y() - icon_size // 2, icon_size, icon_size),
            )

    def mouseReleaseEvent(self, event) -> None:  # noqa: N802
        section = self.logicalIndexAt(event.position().toPoint())
        owner = self.window()
        if isinstance(owner, MainWindow):
            metadata_start = 4
            metadata_end = metadata_start + len(owner.custom_business_metadata_columns)
            if metadata_start <= section < metadata_end:
                column_name = owner.custom_business_metadata_columns[section - metadata_start]
                # Event coordinates are viewport-relative. sectionPosition() is
                # content-relative, so it becomes incorrect after horizontal scrolling.
                section_left = self.sectionViewportPosition(section)
                if (
                    owner.is_manual_business_metadata_column(column_name)
                    and event.position().x() >= section_left + self.sectionSize(section) - 24
                ):
                    owner.remove_custom_business_metadata_column(column_name)
                    event.accept()
                    return
                replicate_icon_left = section_left + 5
                replicate_icon_right = replicate_icon_left + 14
                if (
                    owner.archive_source_mode.currentData() == "folder"
                    and replicate_icon_left <= event.position().x() <= replicate_icon_right
                ):
                    owner.replicate_metadata_from_header(column_name)
                    event.accept()
                    return
        super().mouseReleaseEvent(event)


class MainWindow(QMainWindow):
    connectivity_result = Signal(bool)

    def __init__(self) -> None:
        super().__init__()
        self.settings_store = QSettings(APP_ORG, APP_NAME)
        self.loaded_config_values: dict[str, str | int] = {}
        self.config_loaded = False
        self._proxy_environment_previous: dict[str, str | None] = {}
        self.thread: QThread | None = None
        self.worker: Worker | None = None
        self.task_lock = threading.Lock()
        self.root_folder: Path | None = None
        self.current_run_id: int | None = None
        self.current_log_file: Path | None = None
        # Encrypting logs uses PBKDF2 and disk synchronization. Keep it on a
        # dedicated background thread so archive start and UI updates stay responsive.
        self._support_log_queue: queue.Queue[tuple[Path, str] | None] = queue.Queue()
        self._support_log_writer_thread = threading.Thread(
            target=self._support_log_writer_loop,
            name="archive-support-log-writer",
            daemon=True,
        )
        self._support_log_writer_thread.start()
        self.tasks: list[ArchiveTask] = []
        self.data_definition_files: list[Path] = []
        self.data_definition_root_folder: Path | None = None
        # Config columns are mandatory and cannot be removed. Manual columns
        # are optional and are the only metadata columns with a remove icon.
        self.system_business_metadata_columns: list[str] = [WINDOWS_USER_METADATA_COLUMN]
        self.windows_user_name = getpass.getuser().strip() or os.environ.get("USERNAME", "Unknown Windows User")
        self.authorized_users: list[str] = []
        self.config_business_metadata_columns: list[str] = []
        self.manual_business_metadata_columns: list[str] = []
        self.custom_business_metadata_columns: list[str] = []
        self.custom_business_metadata_values: dict[str, dict[str, str]] = {}
        self.history_db = ArchiveHistoryDatabase(db_file_path())
        self.summary_value_labels: dict[str, QLabel] = {}
        self.summary_subtitle_labels: dict[str, QLabel] = {}
        self.history_value_labels: dict[str, QLabel] = {}
        self.history_subtitle_labels: dict[str, QLabel] = {}
        self.analytics_menu: QListWidget | None = None
        self.analytics_detail_title: QLabel | None = None
        self.analytics_row_count_label: QLabel | None = None
        self.analytics_detail_table: QTableWidget | None = None
        self.analytics_logs_table: QTableWidget | None = None
        self.download_selected_log_btn: QPushButton | None = None
        self.download_selected_logs_zip_btn: QPushButton | None = None
        self.analytics_log_checkbox_column = 0
        self.analytics_checked_logs: set[str] = set()
        self.analytics_log_files: list[Path] = []
        self.analytics_checkbox_press_state: tuple[int, Qt.CheckState] | None = None
        self.history_checkbox_column = 0
        self.history_checked_keys: set[tuple[str, ...]] = set()
        self.loading_history_table = False
        self.query_applied = False
        self.history_export_columns = [
            "Run ID",
            "File Name",
            "Full Path",
            "Size",
            "File Hash",
            "Task ID",
            "Status",
            "Archival Timestamp",
        ]
        self.status_timer = QTimer(self)
        self.status_timer.setInterval(1000)
        self.status_timer.timeout.connect(self.auto_refresh_status)
        self.query_applied = False
        self.moved_task_rows: set[int] = set()
        self.post_run_refresh_timer = QTimer(self)
        self.post_run_refresh_timer.setSingleShot(True)
        self.post_run_refresh_timer.timeout.connect(self.finalize_post_run_refresh)
        self.post_run_warning_timer = QTimer(self)
        self.post_run_warning_timer.setSingleShot(True)
        self.post_run_warning_timer.timeout.connect(self.show_post_run_countdown)
        self.countdown_timer = QTimer(self)
        self.countdown_timer.setInterval(1000)
        self.countdown_timer.timeout.connect(self.update_refresh_notice_banner)
        self.countdown_remaining = 0
        self.waiting_for_network = False
        self._connectivity_check_in_progress = False
        self.connectivity_result.connect(self._on_connectivity_result)

        self.setWindowTitle("Archive Transfer Manager")
        self.setMinimumSize(1500, 950)
        self.resize(1600, 980)
        self.setWindowState(self.windowState() | Qt.WindowMaximized)

        self.tabs = QTabWidget()
        self.create_data_definition_tab()
        self.create_transfer_tab()
        self.create_history_tab()
        self.create_analytics_tab()
        self.create_settings_tab()
        self.setCentralWidget(self.tabs)

        self.showMaximized()

        self.load_settings()
        self._apply_config_gate()
        self.update_summary_cards()
        self.apply_styles()
        self.keyword_input.textChanged.connect(self.load_history_tables)
        # Show the main window first. History reads and initial connectivity
        # probing run on the next event-loop turn, after the splash is closed.
        QTimer.singleShot(0, self._finish_startup)

    def _finish_startup(self) -> None:
        self.load_history_tables()
        self.refresh_analytics_panel()
        self.status_timer.start()
        self.auto_refresh_status()

    def _apply_config_gate(self) -> None:
        """Keep the tab reachable while covering its controls until config is loaded."""
        configured = self.config_loaded
        tab_index = self.tabs.indexOf(self.data_definition_tab)
        if tab_index >= 0:
            self.tabs.setTabEnabled(tab_index, True)
            self.tabs.setTabToolTip(tab_index, "")
        self.data_definition_content.setEnabled(configured)
        self.config_required_overlay.setVisible(not configured)
        if not configured:
            self.config_required_overlay.raise_()

    def create_data_definition_tab(self) -> None:
        self.data_definition_tab = QWidget()
        layout = QVBoxLayout(self.data_definition_tab)
        layout.setContentsMargins(0, 0, 0, 0)
        self.data_definition_content = QWidget()
        content_layout = QVBoxLayout(self.data_definition_content)
        content_layout.setSpacing(10)

        title_label = QLabel("Data Definition")
        title_label.setObjectName("dashboardTitle")
        subtitle_label = QLabel("Select a single file or a folder, review the discovered files, and remove any files before transfer.")
        subtitle_label.setObjectName("refreshLabel")
        content_layout.addWidget(title_label)
        content_layout.addWidget(subtitle_label)

        source_selector_frame = QFrame()
        source_selector_frame.setObjectName("archiveSourceFrame")
        selection_layout = QHBoxLayout(source_selector_frame)
        selection_layout.setContentsMargins(14, 10, 14, 10)
        selection_layout.setSpacing(12)
        source_text_layout = QVBoxLayout()
        source_label = QLabel("Archive Source")
        source_label.setObjectName("archiveSourceLabel")
        source_hint = QLabel("Choose the data you want to prepare for archival")
        source_hint.setObjectName("archiveSourceHint")
        source_text_layout.addWidget(source_label)
        source_text_layout.addWidget(source_hint)
        self.archive_source_mode = QComboBox()
        self.archive_source_mode.setObjectName("archiveSourceMode")
        down_icon_path = Path(__file__).resolve().parent / "down.svg"
        if down_icon_path.is_file():
            self.archive_source_mode.setStyleSheet(
                f"QComboBox::down-arrow {{ image: url({down_icon_path.as_posix()}); width: 14px; height: 14px; }}"
            )
        self.archive_source_mode.addItem("Whole Folder", "folder")
        self.archive_source_mode.addItem("Single File", "file")
        self.archive_source_mode.currentIndexChanged.connect(self.on_archive_source_mode_changed)
        selection_layout.addLayout(source_text_layout)
        selection_layout.addStretch()
        selection_layout.addWidget(self.archive_source_mode)
        content_layout.addWidget(source_selector_frame)

        source_layout = QHBoxLayout()
        self.folder_input = QLineEdit()
        self.folder_input.setPlaceholderText("Select a folder to prepare, including all files in its subfolders")
        self.browse_source_btn = QPushButton("Select Folder")
        self.browse_source_btn.clicked.connect(self.select_archive_source)
        source_layout.addWidget(self.folder_input)
        source_layout.addWidget(self.browse_source_btn)
        content_layout.addLayout(source_layout)

        review_header_layout = QHBoxLayout()
        review_label = QLabel("Files Prepared for Transfer")
        review_label.setObjectName("sectionLabel")
        self.metadata_import_selector = QComboBox()
        self.metadata_import_selector.setObjectName("metadataImportSelector")
        self.metadata_import_selector.setToolTip(
            "Choose one metadata source. CSV/Excel imports values by File Name; JSON adds empty column names."
        )
        if down_icon_path.is_file():
            self.metadata_import_selector.setStyleSheet(
                f"QComboBox::down-arrow {{ image: url({down_icon_path.as_posix()}); width: 14px; height: 14px; }}"
            )
        self.metadata_import_selector.addItem("Load Business Metadata", None)
        self.metadata_import_selector.addItem("Load CSV / Excel Metadata Sheet", "sheet")
        self.metadata_import_selector.currentIndexChanged.connect(self.on_metadata_import_selected)
        self.metadata_import_selector.setVisible(False)

        self.add_metadata_column_btn = QPushButton("Add Manual Column")
        self.add_metadata_column_btn.setObjectName("secondaryActionButton")
        self.add_metadata_column_btn.setToolTip("Add one additional business metadata column manually.")
        self.add_metadata_column_btn.clicked.connect(self.add_custom_business_metadata_column)
        review_header_layout.addWidget(review_label)
        review_header_layout.addStretch()
        review_header_layout.addWidget(self.metadata_import_selector)
        review_header_layout.addWidget(self.add_metadata_column_btn)
        self.data_definition_table = QTableWidget()
        self.data_definition_table.setColumnCount(4)
        self.data_definition_table.setHorizontalHeaderLabels(["Action", "File Name", "Full Path", "Size"])
        self.data_definition_table.setAlternatingRowColors(True)
        self.data_definition_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.data_definition_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.data_definition_table.setWordWrap(False)
        self.data_definition_table.setHorizontalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        self.data_definition_table.setHorizontalHeader(MetadataHeader(self.data_definition_table, self.data_definition_table))
        self._apply_data_definition_column_widths()
        content_layout.addLayout(review_header_layout)
        content_layout.addWidget(self.data_definition_table, 1)

        action_layout = QHBoxLayout()
        self.refresh_data_definition_btn = QPushButton("Refresh Data Definition")
        self.refresh_data_definition_btn.setObjectName("secondaryActionButton")
        self.refresh_data_definition_btn.setToolTip(
            "Clear the selected source, prepared files, manual metadata columns, and entered metadata values."
        )
        self.refresh_data_definition_btn.clicked.connect(self.reset_data_definition_page)
        self.move_to_transfers_btn = QPushButton("Move to Transfers")
        self.move_to_transfers_btn.clicked.connect(self.move_data_definition_to_transfers)
        action_layout.addStretch()
        action_layout.addWidget(self.refresh_data_definition_btn)
        action_layout.addWidget(self.move_to_transfers_btn)
        content_layout.addLayout(action_layout)

        layout.addWidget(self.data_definition_content)
        self.config_required_overlay = QFrame(self.data_definition_tab)
        self.config_required_overlay.setObjectName("configRequiredOverlay")
        overlay_layout = QVBoxLayout(self.config_required_overlay)
        overlay_layout.setContentsMargins(32, 32, 32, 32)
        overlay_layout.setAlignment(Qt.AlignCenter)
        overlay_title = QLabel("Configuration Required")
        overlay_title.setObjectName("configRequiredOverlayTitle")
        overlay_title.setAlignment(Qt.AlignCenter)
        overlay_message = QLabel("Upload config.json in Settings to start with Data Definition for archival.")
        overlay_message.setObjectName("configRequiredOverlayMessage")
        overlay_message.setAlignment(Qt.AlignCenter)
        overlay_message.setWordWrap(True)
        go_to_settings_btn = QPushButton("Go to Settings")
        go_to_settings_btn.setObjectName("secondaryActionButton")
        go_to_settings_btn.clicked.connect(lambda: self.tabs.setCurrentWidget(self.settings_tab))
        overlay_layout.addWidget(overlay_title)
        overlay_layout.addWidget(overlay_message)
        overlay_layout.addWidget(go_to_settings_btn, 0, Qt.AlignCenter)
        self.config_required_overlay.setGeometry(self.data_definition_tab.rect())
        self.config_required_overlay.raise_()
        self.tabs.addTab(self.data_definition_tab, "Data Definition")

    def create_transfer_tab(self) -> None:
        self.transfer_tab = QWidget()
        layout = QVBoxLayout()
        layout.setSpacing(10)

        header_layout = QHBoxLayout()
        title_layout = QVBoxLayout()
        title_label = QLabel("Upload Status Monitor")
        title_label.setObjectName("dashboardTitle")
        self.live_badge = QLabel("Live")
        self.live_badge.setObjectName("liveBadge")
        self.last_refresh_label = QLabel("Last refreshed: --")
        self.last_refresh_label.setObjectName("refreshLabel")

        title_row = QHBoxLayout()
        title_row.addWidget(title_label)
        title_row.addWidget(self.live_badge)
        title_row.addStretch()
        title_layout.addLayout(title_row)
        title_layout.addWidget(self.last_refresh_label)

        self.refresh_notice_banner = QLabel()
        self.refresh_notice_banner.setObjectName("refreshNoticeBanner")
        self.refresh_notice_banner.setWordWrap(True)
        self.refresh_notice_banner.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Preferred)
        self.refresh_notice_banner.setVisible(False)

        self.proxy_toggle_btn = QPushButton("Proxy: Off")
        self.proxy_toggle_btn.setObjectName("proxyToggleButton")
        self.proxy_toggle_btn.setCheckable(True)
        self.proxy_toggle_btn.setToolTip("Enable or disable use of the Proxy URL configured in Settings")
        self.proxy_toggle_btn.toggled.connect(self.on_proxy_toggled)

        self.refresh_summary_btn = QPushButton("Refresh")
        self.refresh_summary_btn.clicked.connect(self.refresh_monitor)

        header_layout.addLayout(title_layout)
        header_layout.addWidget(self.refresh_notice_banner, 1)
        header_layout.addWidget(self.proxy_toggle_btn)
        header_layout.addWidget(self.refresh_summary_btn)

        self.archive_starting_banner = QLabel()
        self.archive_starting_banner.setObjectName("archiveStartingBanner")
        self.archive_starting_banner.setWordWrap(True)
        self.archive_starting_banner.setVisible(False)

        self.summary_cards_layout = QHBoxLayout()
        self.summary_cards_layout.setSpacing(10)
        self._create_summary_card(
            self.summary_cards_layout,
            self.summary_value_labels,
            self.summary_subtitle_labels,
            "total",
            "TOTAL UPLOADS",
            "#0b1437",
        )
        self._create_summary_card(
            self.summary_cards_layout,
            self.summary_value_labels,
            self.summary_subtitle_labels,
            "successful",
            "SUCCESSFUL",
            "#14a36c",
        )
        self._create_summary_card(
            self.summary_cards_layout,
            self.summary_value_labels,
            self.summary_subtitle_labels,
            "in_progress",
            "IN PROGRESS",
            "#1890c8",
        )
        self._create_summary_card(
            self.summary_cards_layout,
            self.summary_value_labels,
            self.summary_subtitle_labels,
            "failed",
            "FAILED",
            "#e1525c",
        )

        self.overall_label = QLabel("Overall Progress")
        self.overall_label.setObjectName("sectionLabel")
        self.overall_progress = QProgressBar()
        self.overall_progress.setValue(0)

        self.table = QTableWidget()
        self.table.setColumnCount(6)
        self.table.setHorizontalHeaderLabels(
            [
                "Relative Path",
                "Size",
                "Task ID",
                "Progress",
                "Status",
                "Actions",
            ]
        )
        header = self.table.horizontalHeader()
        for column in range(6):
            header.setSectionResizeMode(column, QHeaderView.Stretch)
        self.table.setAlternatingRowColors(True)
        self.table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.ExtendedSelection)
        self.table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.table.customContextMenuRequested.connect(self.show_task_context_menu)
        self.table.setEditTriggers(QAbstractItemView.NoEditTriggers)

        actions_layout = QHBoxLayout()
        self.start_btn = QPushButton("Start Archiving")
        self.start_btn.clicked.connect(self.start_processing)
        self.refresh_btn = QPushButton("Review Data Definition")
        self.refresh_btn.clicked.connect(lambda: self.tabs.setCurrentWidget(self.data_definition_tab))
        actions_layout.addWidget(self.start_btn)
        actions_layout.addWidget(self.refresh_btn)
        actions_layout.addStretch()

        layout.addLayout(header_layout)
        layout.addWidget(self.archive_starting_banner)
        layout.addLayout(self.summary_cards_layout)
        layout.addWidget(self.overall_label)
        layout.addWidget(self.overall_progress)
        layout.addWidget(self.table)
        layout.addLayout(actions_layout)

        self.transfer_tab.setLayout(layout)
        self.tabs.addTab(self.transfer_tab, "Transfers")

    def create_history_tab(self) -> None:
        self.history_tab = QWidget()
        layout = QVBoxLayout()
        layout.setSpacing(10)

        header_layout = QHBoxLayout()
        title_layout = QVBoxLayout()
        history_title = QLabel("Archive History")
        history_title.setObjectName("dashboardTitle")
        history_subtitle = QLabel("History table with search, filters, and query builder")
        history_subtitle.setObjectName("refreshLabel")
        title_layout.addWidget(history_title)
        title_layout.addWidget(history_subtitle)

        self.refresh_history_btn = QPushButton("Refresh History")
        self.refresh_history_btn.clicked.connect(self.load_history_tables)

        header_layout.addLayout(title_layout)
        header_layout.addStretch()
        header_layout.addWidget(self.refresh_history_btn)

        toolbar_layout = QHBoxLayout()
        toolbar_layout.setSpacing(10)

        self.keyword_input = QLineEdit()
        self.keyword_input.setPlaceholderText("Keyword")

        self.build_query_btn = QPushButton("Build Query")
        self.build_query_btn.setObjectName("warningOutlineButton")
        self.build_query_btn.clicked.connect(self.show_query_builder)

        self.close_query_btn = QPushButton("Close")
        self.close_query_btn.setObjectName("closeQueryButton")
        self.close_query_btn.setVisible(False)
        self.close_query_btn.clicked.connect(self.hide_query_builder)

        self.export_history_btn = QPushButton("Export")
        self.export_history_btn.setObjectName("violetOutlineButton")
        self.export_history_btn.clicked.connect(self.export_history_table)

        self.filter_columns_btn = QPushButton("Filter Columns")
        self.filter_columns_btn.setObjectName("filterColumnsButton")
        self.filter_columns_popup = QFrame(self, Qt.Popup)
        self.filter_columns_popup.setObjectName("filterColumnsPopup")
        self.filter_columns_popup.setFrameShape(QFrame.StyledPanel)
        self.filter_columns_popup.setMinimumWidth(220)
        self.filter_columns_btn.clicked.connect(self.toggle_filter_columns_menu)
        self.column_controls: dict[int, SvgToggleButton] = {}
        self._initialize_filter_column_menu()

        toolbar_layout.addWidget(self.keyword_input, 1)
        toolbar_layout.addWidget(self.build_query_btn)
        toolbar_layout.addWidget(self.close_query_btn)
        toolbar_layout.addWidget(self.export_history_btn)
        toolbar_layout.addWidget(self.filter_columns_btn)

        self.query_builder_frame = QFrame()
        self.query_builder_frame.setObjectName("queryBuilderFrame")
        query_builder_layout = QVBoxLayout(self.query_builder_frame)
        query_builder_layout.setContentsMargins(12, 12, 12, 12)
        query_builder_layout.setSpacing(10)

        query_actions_layout = QHBoxLayout()
        self.add_clause_btn = QPushButton("Add New Clause")
        self.add_clause_btn.setObjectName("blueOutlineButton")
        self.add_clause_btn.clicked.connect(self.add_query_clause)
        self.run_query_btn = QPushButton("Run Query")
        self.run_query_btn.setObjectName("successOutlineButton")
        self.run_query_btn.clicked.connect(self.run_history_query)
        query_actions_layout.addWidget(self.add_clause_btn)
        query_actions_layout.addWidget(self.run_query_btn)
        query_actions_layout.addStretch()

        self.query_table = QTableWidget()
        self.query_table.setColumnCount(5)
        self.query_table.setHorizontalHeaderLabels(["And/Or", "Field", "Operator", "Value", "Remove"])
        for column in range(self.query_table.columnCount()):
            self.query_table.horizontalHeader().setSectionResizeMode(column, QHeaderView.Stretch)
        self.query_table.verticalHeader().setVisible(False)
        self.query_table.setAlternatingRowColors(True)
        self.query_table.setSelectionMode(QAbstractItemView.NoSelection)
        self.query_table.setEditTriggers(QAbstractItemView.NoEditTriggers)

        query_builder_layout.addLayout(query_actions_layout)
        query_builder_layout.addWidget(self.query_table)
        self.query_builder_frame.setVisible(False)
        self.add_query_clause()

        self.active_query_note = QLabel("")
        self.active_query_note.setObjectName("queryNoteLabel")
        self.active_query_note.setVisible(False)

        self.clear_filter_btn = QPushButton("Clear Filters")
        self.clear_filter_btn.clicked.connect(self.clear_history_filters)
        toolbar_layout.addWidget(self.clear_filter_btn)

        history_label = QLabel("Archived Files")
        history_label.setObjectName("sectionLabel")
        self.history_table = QTableWidget()
        self.history_table.setColumnCount(9)
        self.history_table.setHorizontalHeaderLabels(["", "Run ID", "File Name", "Full Path", "Size", "File Hash", "Task ID", "Status", "Archival Timestamp"])
        history_header = CheckboxHeaderView(self.history_checkbox_column, self.history_table)
        self.history_table.setHorizontalHeader(history_header)
        self.history_select_all_checkbox = history_header.select_all_checkbox
        self.history_select_all_checkbox.clicked.connect(self.on_history_header_checkbox_clicked)
        self._apply_history_table_column_widths()
        self.history_table.setAlternatingRowColors(True)
        self.history_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.history_table.setSelectionBehavior(QAbstractItemView.SelectRows)

        layout.addLayout(header_layout)
        layout.addLayout(toolbar_layout)
        layout.addWidget(self.query_builder_frame)
        layout.addWidget(self.active_query_note)
        layout.addWidget(history_label)
        layout.addWidget(self.history_table)
        self.history_tab.setLayout(layout)
        self.tabs.addTab(self.history_tab, "History")

    def create_analytics_tab(self) -> None:
        self.analytics_tab = QWidget()
        layout = QVBoxLayout()
        layout.setContentsMargins(12, 12, 12, 12)
        layout.setSpacing(12)

        header_layout = QHBoxLayout()
        title_layout = QVBoxLayout()
        analytics_title = QLabel("Archival Analytics")
        analytics_title.setObjectName("dashboardTitle")
        analytics_subtitle = QLabel("Browse archived, failed, cancelled, pending files, and downloadable protected logs")
        analytics_subtitle.setObjectName("refreshLabel")
        title_layout.addWidget(analytics_title)
        title_layout.addWidget(analytics_subtitle)

        self.refresh_analytics_btn = QPushButton("Refresh Analytics")
        self.refresh_analytics_btn.clicked.connect(self.refresh_analytics_panel)

        header_layout.addLayout(title_layout, 1)
        header_layout.addStretch()
        header_layout.addWidget(self.refresh_analytics_btn)

        navigation_frame = QFrame()
        navigation_frame.setObjectName("analyticsNavFrame")
        navigation_layout = QVBoxLayout(navigation_frame)
        navigation_layout.setContentsMargins(0, 0, 0, 0)
        navigation_layout.setSpacing(8)

        menu_title = QLabel("Navigation")
        menu_title.setObjectName("sectionLabel")
        navigation_layout.addWidget(menu_title)

        self.analytics_menu = QListWidget()
        self.analytics_menu.setObjectName("analyticsMenu")
        self.analytics_menu.setAlternatingRowColors(False)
        self.analytics_menu.setUniformItemSizes(True)
        self.analytics_menu.setMinimumWidth(220)
        self.analytics_menu.setMaximumWidth(260)
        for label, key in [
            ("Archived Files", "archived"),
            ("Failed Files", "failed"),
            ("Cancelled Files", "canceled"),
            ("Pending Files", "pending"),
            ("Download Logs", "logs"),
        ]:
            item = QListWidgetItem(label)
            item.setData(Qt.UserRole, key)
            self.analytics_menu.addItem(item)
        self.analytics_menu.currentItemChanged.connect(self.on_analytics_menu_changed)
        navigation_layout.addWidget(self.analytics_menu, 1)

        detail_frame = QFrame()
        detail_frame.setObjectName("analyticsDetailFrame")
        detail_layout = QVBoxLayout(detail_frame)
        detail_layout.setContentsMargins(12, 12, 12, 12)
        detail_layout.setSpacing(10)

        self.analytics_detail_title = QLabel("Details")
        self.analytics_detail_title.setObjectName("sectionLabel")
        self.analytics_row_count_label = QLabel("0 rows")
        self.analytics_row_count_label.setObjectName("analyticsRowCount")
        self.analytics_row_count_label.setAlignment(Qt.AlignRight | Qt.AlignVCenter)

        detail_header_layout = QHBoxLayout()
        detail_header_layout.setContentsMargins(0, 0, 0, 0)
        detail_header_layout.addWidget(self.analytics_detail_title)
        detail_header_layout.addStretch()
        detail_header_layout.addWidget(self.analytics_row_count_label)

        self.analytics_detail_table = QTableWidget()
        self.analytics_detail_table.setColumnCount(6)
        self.analytics_detail_table.setHorizontalHeaderLabels(["Run ID", "File Name", "Full Path", "Status", "Task ID", "Archived On"])
        for column in range(self.analytics_detail_table.columnCount()):
            self.analytics_detail_table.horizontalHeader().setSectionResizeMode(column, QHeaderView.Stretch)
        self.analytics_detail_table.verticalHeader().setVisible(False)
        self.analytics_detail_table.setAlternatingRowColors(True)
        self.analytics_detail_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.analytics_detail_table.setSelectionBehavior(QAbstractItemView.SelectRows)

        self.analytics_logs_table = QTableWidget()
        self.analytics_logs_table.setColumnCount(4)
        self.analytics_logs_table.setHorizontalHeaderLabels(["File Name", "Modified", "Size", "Download"])
        for column in range(self.analytics_logs_table.columnCount()):
            self.analytics_logs_table.horizontalHeader().setSectionResizeMode(column, QHeaderView.Stretch)
        self.analytics_logs_table.verticalHeader().setVisible(False)
        self.analytics_logs_table.setAlternatingRowColors(True)
        self.analytics_logs_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.analytics_logs_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.analytics_logs_table.hide()

        detail_layout.addLayout(detail_header_layout)
        detail_layout.addWidget(self.analytics_detail_table, 1)
        detail_layout.addWidget(self.analytics_logs_table, 1)

        content_layout = QHBoxLayout()
        content_layout.setContentsMargins(0, 0, 0, 0)
        content_layout.setSpacing(12)
        content_layout.addWidget(navigation_frame, 0)
        content_layout.addWidget(detail_frame, 1)

        content_widget = QWidget()
        content_widget.setLayout(content_layout)

        layout.addLayout(header_layout)
        layout.addWidget(content_widget, 1)

        self.analytics_tab.setLayout(layout)
        self.tabs.addTab(self.analytics_tab, "Analytics")

    def create_settings_tab(self) -> None:
        self.settings_tab = QWidget()
        outer_layout = QVBoxLayout()
        outer_layout.setSpacing(12)

        config_group = QGroupBox("Configuration File")
        config_layout = QHBoxLayout(config_group)
        self.config_file_input = QLineEdit()
        self.config_file_input.setReadOnly(True)
        self.config_file_input.setPlaceholderText("Upload an encrypted configuration ZIP bundle (.zip)")
        self.upload_config_btn = QPushButton("Upload Encrypted Config ZIP")
        self.upload_config_btn.clicked.connect(self.load_config_file)
        config_layout.addWidget(self.config_file_input)
        config_layout.addWidget(self.upload_config_btn)

        form_layout = QFormLayout()
        form_layout.setFieldGrowthPolicy(QFormLayout.ExpandingFieldsGrow)

        self.auth_server_input = QLineEdit()
        self.archive_service_url_input = QLineEdit()
        self.client_app_id_input = QLineEdit()
        self.client_secret_input = QLineEdit()
        self.client_secret_input.setEchoMode(QLineEdit.Password)
        self.archive_service_app_id_input = QLineEdit()
        self.proxy_url_input = QLineEdit()
        self.proxy_url_input.setEchoMode(QLineEdit.Password)
        self.proxy_url_input.setToolTip("The proxy URL is masked for security.")
        self.data_owner_input = QLineEdit()
        self.country_input = QLineEdit()
        self.data_classification_input = QLineEdit()
        self.retention_policy_input = QLineEdit()
        self.required_retrieval_time_input = QLineEdit()

        self.retry_count = QSpinBox()
        self.retry_count.setRange(1, 20)
        self.chunk_size = QSpinBox()
        self.chunk_size.setRange(1, 1024)
        self.chunk_size.setSuffix(" MB")

        self._set_settings_inputs_read_only(True)

        form_layout.addRow("Auth Server URL", self.auth_server_input)
        form_layout.addRow("Archive Service URL", self.archive_service_url_input)
        form_layout.addRow("Client App ID", self.client_app_id_input)
        form_layout.addRow("Client Secret", self.client_secret_input)
        form_layout.addRow("Archive Service App ID", self.archive_service_app_id_input)
        form_layout.addRow("Proxy URL", self.proxy_url_input)
        form_layout.addRow("Retries", self.retry_count)
        form_layout.addRow("Chunk Size", self.chunk_size)
        form_layout.addRow("Data Owner", self.data_owner_input)
        form_layout.addRow("Country", self.country_input)
        form_layout.addRow("Data Classification", self.data_classification_input)
        form_layout.addRow("Retention Policy", self.retention_policy_input)
        form_layout.addRow("Required Retrieval Time", self.required_retrieval_time_input)

        save_btn = QPushButton("Save Settings")
        save_btn.clicked.connect(lambda: self.save_settings(show_message=True))
        self.factory_reset_btn = QPushButton("Factory Reset Application")
        self.factory_reset_btn.setObjectName("dangerActionButton")
        self.factory_reset_btn.setToolTip(
            "Clear the loaded configuration and all saved application settings from the UI and local settings store."
        )
        self.factory_reset_btn.clicked.connect(self.factory_reset_application)

        settings_actions_layout = QHBoxLayout()
        settings_actions_layout.setSpacing(10)
        settings_actions_layout.addWidget(save_btn)
        settings_actions_layout.addWidget(self.factory_reset_btn)

        outer_layout.addWidget(config_group)
        outer_layout.addLayout(form_layout)
        outer_layout.addLayout(settings_actions_layout)

        self.settings_tab.setLayout(outer_layout)
        self.tabs.addTab(self.settings_tab, "Settings")

    def _current_archive_run_rows(self) -> list[sqlite3.Row]:
        """Return persisted task rows only for the currently active archive run."""
        if self.current_run_id is None:
            return []
        return [
            row
            for row in self.history_db.fetch_task_history(limit=1000)
            if int(row["run_id"]) == self.current_run_id
        ]

    @staticmethod
    def _is_pending_archive_row(row: sqlite3.Row) -> bool:
        return str(row["status"]) in {
            "Queued", "Ready", "Preparing", "Uploading", WAITING_FOR_NETWORK_STATUS
        }

    def refresh_analytics_panel(self) -> None:
        if self.analytics_menu is None:
            return

        rows = self.history_db.fetch_task_history(limit=1000)
        current_run_rows = self._current_archive_run_rows()
        counts = {
            "archived": sum(1 for row in rows if str(row["archived_at"]).strip() not in {"", "-"}),
            "failed": sum(1 for row in rows if str(row["status"]) == "Failed"),
            "canceled": sum(1 for row in rows if str(row["status"]) == "Canceled"),
            # Pending is a live operational view, never a mixed list of old runs.
            "pending": sum(1 for row in current_run_rows if self._is_pending_archive_row(row)),
            "logs": sum(1 for _ in self.logs_directory().glob("*.log.enc")),
        }
        labels = {
            "archived": "Archived Files",
            "failed": "Failed Files",
            "canceled": "Cancelled Files",
            "pending": "Pending Files",
            "logs": "Download Logs",
        }

        current_item = self.analytics_menu.currentItem()
        current_key = current_item.data(Qt.UserRole) if current_item is not None else None
        signal_blocker = QSignalBlocker(self.analytics_menu)
        for index in range(self.analytics_menu.count()):
            item = self.analytics_menu.item(index)
            key = item.data(Qt.UserRole)
            item.setText(f"{labels[key]} ({counts[key]})")
        del signal_blocker

        if current_key is None and self.analytics_menu.count() > 0:
            self.analytics_menu.setCurrentRow(0)
            return
        if current_item is not None:
            self.on_analytics_menu_changed(current_item, None)

    def on_analytics_menu_changed(self, current: QListWidgetItem | None, _previous: QListWidgetItem | None) -> None:
        if current is None:
            return
        section = current.data(Qt.UserRole)
        if section == "logs":
            self.show_logs_panel()
        else:
            self.show_status_detail_panel(str(section))

    def update_analytics_row_count(self, row_count: int) -> None:
        """Show the row total for whichever Analytics detail table is visible."""
        if self.analytics_row_count_label is not None:
            self.analytics_row_count_label.setText(f"{row_count} row" if row_count == 1 else f"{row_count} rows")

    def show_status_detail_panel(self, section: str) -> None:
        if self.analytics_detail_title is None or self.analytics_detail_table is None or self.analytics_logs_table is None:
            return
        title_map = {
            "archived": "Archived Files Details",
            "failed": "Failed Files Details",
            "canceled": "Cancelled Files Details",
            "pending": "Pending Files Details",
        }
        self.analytics_detail_title.setText(title_map.get(section, "Details"))
        self.analytics_detail_table.show()
        self.analytics_logs_table.hide()

        rows = self.history_db.fetch_task_history(limit=1000)
        if section == "archived":
            filtered = [row for row in rows if str(row["archived_at"]).strip() not in {"", "-"}]
        elif section == "failed":
            filtered = [row for row in rows if str(row["status"]) == "Failed"]
        elif section == "canceled":
            filtered = [row for row in rows if str(row["status"]) == "Canceled"]
        else:
            # The Pending Files page is intentionally limited to the current
            # archive run, so historical unfinished tasks are not displayed.
            filtered = [row for row in self._current_archive_run_rows() if self._is_pending_archive_row(row)]

        self.analytics_detail_table.setRowCount(0)
        for row_index, item in enumerate(filtered):
            self.analytics_detail_table.insertRow(row_index)
            values = [
                str(item["run_id"]),
                str(item["file_name"] or Path(str(item["full_path"])).name),
                str(item["full_path"] or item["relative_path"]),
                str(item["status"]),
                str(item["task_id"]),
                str(item["archived_at"]).split(" ")[0],
            ]
            for column, value in enumerate(values):
                table_item = QTableWidgetItem(value)
                table_item.setTextAlignment(Qt.AlignCenter)
                self.analytics_detail_table.setItem(row_index, column, table_item)
        self.analytics_detail_table.resizeRowsToContents()
        self.update_analytics_row_count(self.analytics_detail_table.rowCount())

    def show_logs_panel(self) -> None:
        if self.analytics_detail_title is None or self.analytics_detail_table is None or self.analytics_logs_table is None:
            return
        self.analytics_detail_title.setText("Encrypted Archive Support Log Bundles")
        self.analytics_detail_table.hide()
        self.analytics_logs_table.show()
        self.populate_logs_table()

    def logs_directory(self) -> Path:
        return logs_dir_path()

    def populate_logs_table(self) -> None:
        if self.analytics_logs_table is None:
            return
        # Export only the protected archive logs. Plaintext diagnostic files are
        # intentionally excluded so every downloaded bundle has .log.enc + .salt.
        self.analytics_log_files = sorted(
            self.logs_directory().glob("*.log.enc"),
            key=lambda path: path.stat().st_mtime,
            reverse=True,
        )
        self.analytics_logs_table.blockSignals(True)
        self.analytics_logs_table.setRowCount(0)
        for row_index, log_file in enumerate(self.analytics_log_files):
            self.analytics_logs_table.insertRow(row_index)
            for column, value in enumerate(
                [
                    log_file.name,
                    datetime.fromtimestamp(log_file.stat().st_mtime).strftime("%Y-%m-%d %H:%M:%S"),
                    format_size(log_file.stat().st_size),
                ],
            ):
                table_item = QTableWidgetItem(value)
                table_item.setTextAlignment(Qt.AlignCenter)
                self.analytics_logs_table.setItem(row_index, column, table_item)

            download_btn = QPushButton("Download")
            download_btn.setObjectName("secondaryActionButton")
            download_btn.clicked.connect(lambda _checked=False, file_path=log_file: self.download_log_file(file_path))
            self.analytics_logs_table.setCellWidget(row_index, 3, download_btn)

        self.analytics_logs_table.blockSignals(False)
        self.analytics_logs_table.resizeRowsToContents()
        self.update_analytics_row_count(self.analytics_logs_table.rowCount())

    def on_analytics_log_item_changed(self, item: QTableWidgetItem) -> None:
        if item.column() != self.analytics_log_checkbox_column:
            return
        file_item = self.analytics_logs_table.item(item.row(), 1) if self.analytics_logs_table is not None else None
        if file_item is None:
            return
        file_name = file_item.text()
        if item.checkState() == Qt.Checked:
            self.analytics_checked_logs.add(file_name)
        else:
            self.analytics_checked_logs.discard(file_name)

    def on_analytics_log_cell_pressed(self, index) -> None:
        if self.analytics_logs_table is None:
            return
        if index.column() != self.analytics_log_checkbox_column:
            self.analytics_checkbox_press_state = None
            return
        item = self.analytics_logs_table.item(index.row(), index.column())
        if item is None:
            self.analytics_checkbox_press_state = None
            return
        self.analytics_checkbox_press_state = (index.row(), item.checkState())

    def on_analytics_log_cell_clicked(self, row: int, column: int) -> None:
        if column != self.analytics_log_checkbox_column or self.analytics_logs_table is None:
            self.analytics_checkbox_press_state = None
            return
        item = self.analytics_logs_table.item(row, column)
        if item is None:
            self.analytics_checkbox_press_state = None
            return
        pressed_state = self.analytics_checkbox_press_state
        self.analytics_checkbox_press_state = None
        if pressed_state == (row, item.checkState()):
            item.setCheckState(Qt.Unchecked if item.checkState() == Qt.Checked else Qt.Checked)

    @staticmethod
    def _encrypted_log_bundle_files(log_file: Path) -> list[Path]:
        """Return only a decryptable protected archive-log bundle.

        The export contract is strict: a ZIP always contains an encrypted
        ``.log.enc`` file and the salt that derives its Fernet key. Plaintext
        technical logs are never exported by this action.
        """
        if not log_file.name.endswith(".log.enc"):
            raise ValueError(
                f"Only protected archive logs (*.log.enc) can be exported. Received: {log_file.name}"
            )
        salt_file = log_file.with_suffix(".salt")
        if not salt_file.exists():
            raise FileNotFoundError(
                f"The encrypted log '{log_file.name}' cannot be exported because its required "
                f"salt file is missing: '{salt_file.name}'."
            )
        return [log_file, salt_file]

    def download_log_file(self, log_file: Path) -> None:
        default_name = f"{log_file.stem}_support_bundle.zip"
        zip_path, _ = QFileDialog.getSaveFileName(
            self,
            "Save Support Log Bundle",
            default_name,
            "ZIP Files (*.zip);;All Files (*)",
        )
        if not zip_path:
            return
        try:
            with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as archive:
                for bundle_file in self._encrypted_log_bundle_files(log_file):
                    archive.write(bundle_file, arcname=bundle_file.name)
        except Exception as exc:  # noqa: BLE001
            QMessageBox.critical(self, "Download Failed", f"Unable to create the log bundle.\n{exc}")
            return
        QMessageBox.information(
            self,
            "Download Complete",
            f"Support log bundle saved to:\n{zip_path}\n\n"
            "This ZIP contains the encrypted .log.enc file and its required .salt file.",
        )

    def download_selected_log_file(self) -> None:
        if self.analytics_logs_table is None:
            return
        selected_rows = self.analytics_logs_table.selectionModel().selectedRows()
        if not selected_rows:
            QMessageBox.information(self, "No Log Selected", "Select one log row to download.")
            return
        row = selected_rows[0].row()
        log_file = self.analytics_log_files[row]
        self.download_log_file(log_file)

    def download_checked_logs_as_zip(self) -> None:
        if not self.analytics_checked_logs:
            QMessageBox.information(self, "No Logs Checked", "Check one or more log files to download as a zip archive.")
            return
        zip_path, _ = QFileDialog.getSaveFileName(self, "Save Logs ZIP", "archive_logs.zip", "ZIP Files (*.zip);;All Files (*)")
        if not zip_path:
            return
        try:
            archived_names: set[str] = set()
            with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as archive:
                for log_file in self.analytics_log_files:
                    if log_file.name not in self.analytics_checked_logs:
                        continue
                    for bundle_file in self._encrypted_log_bundle_files(log_file):
                        # A salt file can be shared only by its own encrypted log,
                        # but the guard keeps archives free of duplicate members.
                        if bundle_file.name not in archived_names:
                            archive.write(bundle_file, arcname=bundle_file.name)
                            archived_names.add(bundle_file.name)
        except Exception as exc:  # noqa: BLE001
            QMessageBox.critical(self, "ZIP Download Failed", f"Unable to create zip file.\n{exc}")
            return
        QMessageBox.information(
            self,
            "ZIP Download Complete",
            f"Selected log files saved to:\n{zip_path}\n\n"
            "Every encrypted .log.enc file is included with its matching .salt file.",
        )

    def _create_summary_card(
        self,
        parent_layout: QHBoxLayout,
        value_labels: dict[str, QLabel],
        subtitle_labels: dict[str, QLabel],
        key: str,
        title: str,
        accent_color: str,
    ) -> None:
        frame = QFrame()
        frame.setObjectName("summaryCard")
        frame.setStyleSheet(
            f"QFrame#summaryCard {{background: white; border: 1px solid #d8dbe3; "
            f"border-left: 4px solid {accent_color}; border-radius: 10px; padding: 8px;}}"
        )
        frame.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        layout = QVBoxLayout(frame)
        layout.setContentsMargins(12, 10, 12, 10)
        layout.setSpacing(4)

        title_label = QLabel(title)
        title_label.setObjectName("summaryTitle")
        value_label = QLabel("0")
        value_label.setObjectName("summaryValue")
        subtitle_label = QLabel("No data yet")
        subtitle_label.setObjectName("summarySubtitle")

        layout.addWidget(title_label)
        layout.addWidget(value_label)
        layout.addWidget(subtitle_label)
        parent_layout.addWidget(frame, 1)

        value_labels[key] = value_label
        subtitle_labels[key] = subtitle_label

    def _set_settings_inputs_read_only(self, read_only: bool) -> None:
        line_edits = [
            self.auth_server_input,
            self.archive_service_url_input,
            self.client_app_id_input,
            self.client_secret_input,
            self.archive_service_app_id_input,
            self.proxy_url_input,
            self.data_owner_input,
            self.country_input,
            self.data_classification_input,
            self.retention_policy_input,
            self.required_retrieval_time_input,
        ]
        for field in line_edits:
            field.setReadOnly(read_only)
        self.retry_count.setReadOnly(read_only)
        self.retry_count.setButtonSymbols(QSpinBox.NoButtons if read_only else QSpinBox.UpDownArrows)
        self.chunk_size.setReadOnly(read_only)
        self.chunk_size.setButtonSymbols(QSpinBox.NoButtons if read_only else QSpinBox.UpDownArrows)

    def _apply_settings_map(self, settings_map: dict[str, str | int]) -> None:
        self.auth_server_input.setText(str(settings_map.get("auth_server_url", "")))
        self.archive_service_url_input.setText(str(settings_map.get("archive_service_url", "")))
        self.client_app_id_input.setText(str(settings_map.get("client_app_id", "")))
        self.client_secret_input.setText(str(settings_map.get("client_secret", "")))
        self.archive_service_app_id_input.setText(str(settings_map.get("archive_service_app_id", "")))
        self.proxy_url_input.setText(str(settings_map.get("proxy_url", "")))
        self.retry_count.setValue(int(settings_map.get("retry_count", 3)))
        self.chunk_size.setValue(int(settings_map.get("chunk_size_mb", 50)))
        self.data_owner_input.setText(str(settings_map.get("data_owner", "")))
        self.country_input.setText(str(settings_map.get("country", "")))
        self.data_classification_input.setText(str(settings_map.get("data_classification", "")))
        self.retention_policy_input.setText(str(settings_map.get("retention_policy", "")))
        self.required_retrieval_time_input.setText(str(settings_map.get("required_retrieval_time", "")))

    def load_settings(self) -> None:
        saved_map = {
            "auth_server_url": self.settings_store.value("auth_server_url", ""),
            "archive_service_url": self.settings_store.value("archive_service_url", ""),
            "client_app_id": self.settings_store.value("client_app_id", ""),
            "client_secret": self.settings_store.value("client_secret", ""),
            "archive_service_app_id": self.settings_store.value("archive_service_app_id", ""),
            "proxy_url": self.settings_store.value("proxy_url", ""),
            "proxy_enabled": self.settings_store.value("proxy_enabled", False, type=bool),
            "retry_count": int(self.settings_store.value("retry_count", 3)),
            "chunk_size_mb": int(self.settings_store.value("chunk_size_mb", 50)),
            "data_owner": self.settings_store.value("data_owner", ""),
            "country": self.settings_store.value("country", ""),
            "data_classification": self.settings_store.value("data_classification", ""),
            "retention_policy": self.settings_store.value("retention_policy", ""),
            "required_retrieval_time": self.settings_store.value("required_retrieval_time", ""),
        }
        config_file_path = str(self.settings_store.value("config_file_path", ""))
        stored_metadata_columns = self.settings_store.value("metadata_columns", [], type=list)
        self.authorized_users = self.settings_store.value("authorized_users", [], type=list)
        self.config_business_metadata_columns = self._metadata_columns_from_json(
            {"metadata_columns": stored_metadata_columns}
        ) if stored_metadata_columns else []
        self._rebuild_business_metadata_columns()
        self.config_file_input.setText(config_file_path)
        self.loaded_config_values = dict(saved_map)
        self.config_loaded = bool(config_file_path and str(saved_map["archive_service_url"]).strip())
        self._apply_settings_map(saved_map)
        self.proxy_toggle_btn.setChecked(bool(saved_map["proxy_enabled"]))

    @staticmethod
    def _decrypt_config_bytes(encrypted_data: bytes, salt: bytes) -> dict[str, object]:
        """Decrypt Config@Admin123-protected config bytes using their matching salt."""
        try:
            from cryptography.fernet import Fernet, InvalidToken
        except ImportError as exc:
            raise RuntimeError("Encrypted config files require the cryptography package.") from exc
        if len(salt) != 16:
            raise ValueError("The config salt data is invalid.")
        key = pbkdf2_hmac("sha256", CONFIG_ENCRYPTION_PASSWORD.encode("utf-8"), salt, CONFIG_PBKDF2_ITERATIONS, dklen=32)
        try:
            plaintext = Fernet(base64.urlsafe_b64encode(key)).decrypt(encrypted_data)
        except InvalidToken as exc:
            raise ValueError("The encrypted config could not be decrypted with its matching salt data.") from exc
        parsed = json.loads(plaintext.decode("utf-8"))
        if not isinstance(parsed, dict):
            raise ValueError("The decrypted configuration must contain a JSON object.")
        return parsed

    @classmethod
    def _decrypt_config_file(cls, encrypted_path: Path, salt_path: Path) -> dict[str, object]:
        return cls._decrypt_config_bytes(encrypted_path.read_bytes(), salt_path.read_bytes())

    @classmethod
    def _decrypt_config_zip(cls, zip_path: Path) -> dict[str, object]:
        """Read exactly one encrypted config and its matching salt directly from a ZIP bundle."""
        with zipfile.ZipFile(zip_path, "r") as archive:
            members = [member for member in archive.infolist() if not member.is_dir()]
            if len(members) > 10:
                raise ValueError("The config ZIP contains too many files.")
            encrypted_members = [member for member in members if member.filename.casefold().endswith(".enc")]
            salt_members = [member for member in members if member.filename.casefold().endswith(".salt")]
            if len(encrypted_members) != 1 or len(salt_members) != 1:
                raise ValueError("The config ZIP must contain exactly one .enc file and one matching .salt file.")
            encrypted_member = encrypted_members[0]
            salt_member = salt_members[0]
            if encrypted_member.file_size > 5 * 1024 * 1024 or salt_member.file_size > 1024:
                raise ValueError("The config ZIP contains an invalid encrypted config or salt file size.")
            return cls._decrypt_config_bytes(archive.read(encrypted_member), archive.read(salt_member))

    def load_config_file(self) -> None:
        file_path, _ = QFileDialog.getOpenFileName(
            self,
            "Select Config File",
            "",
            "Encrypted Config ZIP Bundles (*.zip);;All Files (*)",
        )
        if not file_path:
            return
        config_path = Path(file_path)
        if config_path.suffix.casefold() != ".zip":
            QMessageBox.critical(
                self, "Encrypted ZIP Required",
                "Only encrypted configuration ZIP bundles are accepted. Create a ZIP containing exactly one .enc config file and its matching .salt file.",
            )
            return
        try:
            raw_data = self._decrypt_config_zip(config_path)
        except Exception as exc:  # noqa: BLE001
            QMessageBox.critical(self, "Config Error", f"Unable to read or decrypt encrypted config ZIP bundle.\n{exc}")
            return

        if not isinstance(raw_data, dict):
            QMessageBox.critical(self, "Config Error", "The configuration file must contain a JSON object.")
            return
        try:
            config_metadata_columns = self._metadata_columns_from_json(raw_data) if "metadata_columns" in raw_data or "columns" in raw_data else []
            raw_authorized_users = raw_data.get("authorized_users", [])
            if not isinstance(raw_authorized_users, list) or any(not isinstance(user, str) or not user.strip() for user in raw_authorized_users):
                raise ValueError("authorized_users must be a list of non-empty Windows user names.")
            authorized_users = [user.strip() for user in raw_authorized_users]
        except ValueError as exc:
            QMessageBox.critical(self, "Config Error", f"Invalid config authorization or metadata value.\n{exc}")
            return

        settings_map = {
            "auth_server_url": raw_data.get("auth_server_url", ""),
            "archive_service_url": raw_data.get("archive_service_url", ""),
            "client_app_id": raw_data.get("client_app_id", ""),
            "client_secret": raw_data.get("client_secret", ""),
            "archive_service_app_id": raw_data.get("archive_service_app_id", ""),
            "proxy_url": raw_data.get("proxy_url", ""),
            "retry_count": int(raw_data.get("retry_count", 3)),
            "chunk_size_mb": int(raw_data.get("chunk_size_mb", 50)),
            "data_owner": raw_data.get("data_owner", ""),
            "country": raw_data.get("country", ""),
            "data_classification": raw_data.get("data_classification", ""),
            "retention_policy": raw_data.get("retention_policy", ""),
            "required_retrieval_time": raw_data.get("required_retrieval_time", ""),
        }
        self.loaded_config_values = settings_map
        self.config_loaded = True
        self.authorized_users = authorized_users
        self.config_business_metadata_columns = config_metadata_columns
        self.manual_business_metadata_columns = []
        self._rebuild_business_metadata_columns()
        self.custom_business_metadata_values = {}
        if self.data_definition_files:
            self.populate_data_definition_table()
        self.config_file_input.setText(file_path)
        self._apply_settings_map(settings_map)
        self._apply_config_gate()
        QMessageBox.information(self, "Config Loaded", "Encrypted configuration ZIP bundle loaded successfully. Click Save Settings to persist it.")

    def save_settings(self, *, show_message: bool) -> None:
        settings_map = self._settings_map()
        if not any(str(value).strip() for value in settings_map.values()):
            QMessageBox.warning(self, "No Configuration", "Please upload a configuration file first.")
            return
        for key, value in settings_map.items():
            self.settings_store.setValue(key, value)
        self.settings_store.setValue("proxy_enabled", self.proxy_toggle_btn.isChecked())
        self.settings_store.setValue("config_file_path", self.config_file_input.text().strip())
        self.settings_store.setValue("metadata_columns", self.config_business_metadata_columns)
        self.settings_store.setValue("authorized_users", self.authorized_users)
        self.settings_store.sync()
        if show_message:
            QMessageBox.information(self, "Settings Saved", "Archive settings were saved successfully.")

    def factory_reset_application(self) -> None:
        """Offer a selective, confirmed reset for config and stored archive data."""
        if self.is_worker_running():
            QMessageBox.warning(
                self,
                "Archive In Progress",
                "Factory reset is unavailable while an archive run is active.",
            )
            return

        dialog = QDialog(self)
        dialog.setWindowTitle("Factory Reset Application")
        dialog.setModal(True)
        dialog.setMinimumWidth(500)
        layout = QVBoxLayout(dialog)
        message = QLabel(
            "Choose the data to remove. Both options are selected by default. "
            "This action cannot be undone."
        )
        message.setWordWrap(True)
        layout.addWidget(message)

        clear_config_checkbox = QCheckBox(
            "Delete configuration file data currently loaded in the application"
        )
        clear_config_checkbox.setChecked(True)
        clear_archive_checkbox = QCheckBox(
            "Delete all stored archived-file data, archive history, and encrypted logs"
        )
        clear_archive_checkbox.setChecked(True)
        layout.addWidget(clear_config_checkbox)
        layout.addWidget(clear_archive_checkbox)

        buttons_layout = QHBoxLayout()
        buttons_layout.addStretch()
        cancel_button = QPushButton("Cancel")
        reset_button = QPushButton("Factory Reset")
        reset_button.setObjectName("dangerActionButton")
        cancel_button.clicked.connect(dialog.reject)
        reset_button.clicked.connect(dialog.accept)
        buttons_layout.addWidget(cancel_button)
        buttons_layout.addWidget(reset_button)
        layout.addLayout(buttons_layout)

        if dialog.exec() != QDialog.Accepted:
            return
        if not clear_config_checkbox.isChecked() and not clear_archive_checkbox.isChecked():
            QMessageBox.information(
                self,
                "No Reset Options Selected",
                "Select at least one reset option to continue.",
            )
            return

        reset_messages: list[str] = []
        if clear_config_checkbox.isChecked():
            self._set_proxy_environment(False)
            self.proxy_toggle_btn.blockSignals(True)
            self.proxy_toggle_btn.setChecked(False)
            self.proxy_toggle_btn.blockSignals(False)
            self.proxy_toggle_btn.setText("Proxy: Off")
            self.loaded_config_values = {}
            self.config_loaded = False
            self.authorized_users = []
            self.config_business_metadata_columns = []
            self.manual_business_metadata_columns = []
            self._rebuild_business_metadata_columns()
            self.settings_store.clear()
            self.settings_store.sync()
            self.config_file_input.clear()
            self._apply_settings_map({
                "auth_server_url": "",
                "archive_service_url": "",
                "client_app_id": "",
                "client_secret": "",
                "archive_service_app_id": "",
                "proxy_url": "",
                "retry_count": 3,
                "chunk_size_mb": 50,
                "data_owner": "",
                "country": "",
                "data_classification": "",
                "retention_policy": "",
                "required_retrieval_time": "",
            })
            self._set_settings_inputs_read_only(True)
            self._apply_config_gate()
            reset_messages.append("configuration data")

        if clear_archive_checkbox.isChecked():
            try:
                if self.history_db is not None:
                    self.history_db.close()
                storage_dir = app_storage_dir()
                database_path = storage_dir / DB_FILE_NAME
                database_files = [
                    database_path,
                    Path(f"{database_path}-wal"),
                    Path(f"{database_path}-shm"),
                ]
                for database_file in database_files:
                    if database_file.exists():
                        database_file.unlink()
                archive_logs = storage_dir / "archive_logs"
                if archive_logs.exists():
                    shutil.rmtree(archive_logs)
                self.history_db = ArchiveHistoryDatabase(db_file_path())
                self.current_run_id = None
                self.current_log_file = None
                self.tasks = []
                self.table.setRowCount(0)
                self.data_definition_files = []
                self.data_definition_root_folder = None
                self.custom_business_metadata_columns = []
                self.custom_business_metadata_values = {}
                self.data_definition_table.setRowCount(0)
                self._update_metadata_sheet_button_visibility()
                self.load_history_tables()
                self.refresh_analytics_panel()
                self.update_summary_cards()
                self.recalculate_overall_progress()
                reset_messages.append("stored archive data and logs")
            except OSError as exc:
                QMessageBox.critical(
                    self,
                    "Archive Data Reset Failed",
                    f"The archive history or logs could not be removed.\n{exc}",
                )
                return

        QMessageBox.information(
            self,
            "Factory Reset Complete",
            f"Removed: {', '.join(reset_messages)}.",
        )

    def _settings_map(self) -> dict[str, str | int]:
        if self.loaded_config_values:
            return {
                "auth_server_url": self.auth_server_input.text().strip(),
                "archive_service_url": self.archive_service_url_input.text().strip(),
                "client_app_id": self.client_app_id_input.text().strip(),
                "client_secret": self.client_secret_input.text(),
                "archive_service_app_id": self.archive_service_app_id_input.text().strip(),
                "proxy_url": self.proxy_url_input.text().strip(),
                "retry_count": self.retry_count.value(),
                "chunk_size_mb": self.chunk_size.value(),
                "data_owner": self.data_owner_input.text().strip(),
                "country": self.country_input.text().strip(),
                "data_classification": self.data_classification_input.text().strip(),
                "retention_policy": self.retention_policy_input.text().strip(),
                "required_retrieval_time": self.required_retrieval_time_input.text().strip(),
            }
        return {
            "auth_server_url": "",
            "archive_service_url": "",
            "client_app_id": "",
            "client_secret": "",
            "archive_service_app_id": "",
            "proxy_url": "",
            "retry_count": self.retry_count.value(),
            "chunk_size_mb": self.chunk_size.value(),
            "data_owner": "",
            "country": "",
            "data_classification": "",
            "retention_policy": "",
            "required_retrieval_time": "",
        }

    def build_config(self) -> ArchiveConfig:
        settings_map = self._settings_map()
        required_fields = {
            "Auth Server URL": settings_map["auth_server_url"],
            "Archive Service URL": settings_map["archive_service_url"],
            "Client App ID": settings_map["client_app_id"],
            "Client Secret": settings_map["client_secret"],
            "Archive Service App ID": settings_map["archive_service_app_id"],
            "Data Owner": settings_map["data_owner"],
        }
        missing = [label for label, value in required_fields.items() if not str(value).strip()]
        if missing:
            raise ValueError(f"Missing required settings: {', '.join(missing)}")

        return ArchiveConfig(
            auth_server_url=str(settings_map["auth_server_url"]),
            archive_service_url=str(settings_map["archive_service_url"]),
            client_app_id=str(settings_map["client_app_id"]),
            client_secret=str(settings_map["client_secret"]),
            archive_service_app_id=str(settings_map["archive_service_app_id"]),
            proxy_url=str(settings_map["proxy_url"]),
            proxy_enabled=self.proxy_toggle_btn.isChecked(),
            chunk_size_mb=int(settings_map["chunk_size_mb"]),
            retry_count=int(settings_map["retry_count"]),
            data_owner=str(settings_map["data_owner"]),
            country=str(settings_map["country"] or "IN"),
            data_classification=str(settings_map["data_classification"] or "restricted"),
            retention_policy=str(settings_map["retention_policy"] or "1 year"),
            required_retrieval_time=str(settings_map["required_retrieval_time"] or "Instant"),
        )

    def reset_data_definition_page(self) -> None:
        """Restore Data Definition to its default prepared-source state."""
        if self.is_worker_running():
            QMessageBox.information(
                self,
                "Archive In Progress",
                "Data Definition cannot be refreshed while an archive run is active.",
            )
            return
        self.archive_source_mode.blockSignals(True)
        self.archive_source_mode.setCurrentIndex(0)
        self.archive_source_mode.blockSignals(False)
        self.folder_input.clear()
        self.folder_input.setPlaceholderText("Select a folder to prepare, including all files in its subfolders")
        self.browse_source_btn.setText("Select Folder")
        self.data_definition_files = []
        self.data_definition_root_folder = None
        self.manual_business_metadata_columns = []
        self._rebuild_business_metadata_columns()
        self.custom_business_metadata_values = {}
        self.populate_data_definition_table()
        self._update_metadata_sheet_button_visibility()
        self.add_log("Data Definition page refreshed to its default state.")

    def on_archive_source_mode_changed(self) -> None:
        is_single_file = self.archive_source_mode.currentData() == "file"
        self.folder_input.clear()
        self.data_definition_files = []
        self.data_definition_root_folder = None
        self.custom_business_metadata_values = {}
        self.data_definition_table.setRowCount(0)
        self._update_metadata_sheet_button_visibility()
        self.folder_input.setPlaceholderText(
            "Select one file to prepare" if is_single_file else "Select a folder to prepare, including all files in its subfolders"
        )
        self.browse_source_btn.setText("Select File" if is_single_file else "Select Folder")

    def select_archive_source(self) -> None:
        if not self.config_loaded:
            QMessageBox.information(self, "Configuration Required", "Load config.json in Settings before preparing data for archival.")
            self.tabs.setCurrentWidget(self.settings_tab)
            return
        if self.archive_source_mode.currentData() == "file":
            file_path, _ = QFileDialog.getOpenFileName(self, "Select File to Archive", "", "All Files (*)")
            if file_path:
                self.folder_input.setText(file_path)
                self.preview_folder()
            return

        folder = QFileDialog.getExistingDirectory(self, "Select Folder to Archive")
        if folder:
            self.folder_input.setText(folder)
            self.preview_folder()

    def select_folder(self) -> None:
        self.select_archive_source()

    def _create_folder_loading_dialog(self) -> tuple[QDialog, QLabel, QProgressBar]:
        dialog = QDialog(self)
        dialog.setWindowTitle("Loading Folder")
        dialog.setModal(True)
        dialog.setWindowFlags(dialog.windowFlags() & ~Qt.WindowCloseButtonHint)
        dialog.setMinimumWidth(430)
        layout = QVBoxLayout(dialog)
        title = QLabel("Loading folder contents")
        title.setObjectName("folderLoadingTitle")
        message = QLabel("Scanning files and preparing the Data Definition table. Please wait...")
        message.setWordWrap(True)
        progress = QProgressBar()
        progress.setRange(0, 0)
        progress.setTextVisible(False)
        layout.addWidget(title)
        layout.addWidget(message)
        layout.addWidget(progress)
        return dialog, message, progress

    def preview_folder(self) -> None:
        if self.is_worker_running():
            QMessageBox.information(self, "Busy", "Wait for the active archive run to finish before reloading the selected source.")
            return

        source_path = self._validated_source()
        if source_path is None:
            return

        is_single_file = self.archive_source_mode.currentData() == "file"
        loading_dialog: QDialog | None = None
        loading_message: QLabel | None = None
        if is_single_file:
            file_paths = [source_path]
            root_folder = source_path.parent
        else:
            loading_dialog, loading_message, _progress = self._create_folder_loading_dialog()
            loading_dialog.show()
            QApplication.processEvents()
            file_paths = []
            for index, file_path in enumerate(iter_files_recursively(source_path), start=1):
                file_paths.append(file_path)
                if index % 100 == 0:
                    loading_message.setText(
                        f"Scanning files and preparing the Data Definition table... {index} files found"
                    )
                    QApplication.processEvents()
            root_folder = source_path
            loading_message.setText(f"Preparing {len(file_paths)} files for the Data Definition table...")
            QApplication.processEvents()

        self.data_definition_root_folder = root_folder
        self.data_definition_files = file_paths
        self.custom_business_metadata_values = {
            str(file_path): {WINDOWS_USER_METADATA_COLUMN: self.windows_user_name}
            for file_path in file_paths
        }
        self.populate_data_definition_table()
        self._update_metadata_sheet_button_visibility()
        if loading_dialog is not None:
            loading_dialog.close()
        source_description = "selected file" if is_single_file else "selected folder"
        self.add_log(
            f"Discovered {len(self.data_definition_files)} file(s) in the {source_description}: {source_path} "
            f"| Windows user name metadata: {self.windows_user_name}"
        )

    def _update_metadata_sheet_button_visibility(self) -> None:
        """Show metadata-source selection only after a source has been prepared."""
        if not hasattr(self, "metadata_import_selector"):
            return
        can_load = (
            self.data_definition_root_folder is not None
            and bool(self.data_definition_files)
        )
        self.metadata_import_selector.setVisible(can_load)
        self.metadata_import_selector.setEnabled(can_load)
        if not can_load:
            self.metadata_import_selector.blockSignals(True)
            self.metadata_import_selector.setCurrentIndex(0)
            self.metadata_import_selector.blockSignals(False)

    def on_metadata_import_selected(self, _index: int) -> None:
        """Launch one selected source workflow, then reset the selector."""
        source_type = self.metadata_import_selector.currentData()
        if source_type == "sheet":
            self.load_business_metadata_sheet()
        self.metadata_import_selector.blockSignals(True)
        self.metadata_import_selector.setCurrentIndex(0)
        self.metadata_import_selector.blockSignals(False)

    @staticmethod
    def _metadata_sheet_key(value: object) -> str:
        """Normalize a sheet header so File Name/FileName are treated equally."""
        return "".join(character for character in str(value).casefold() if character.isalnum())

    def _read_business_metadata_sheet(self, sheet_path: Path) -> tuple[list[str], list[dict[str, object]]]:
        """Read CSV, XLSX, or XLS sheet data without imposing a fixed metadata schema."""
        suffix = sheet_path.suffix.casefold()
        if suffix == ".csv":
            last_error: UnicodeDecodeError | None = None
            for encoding in ("utf-8-sig", "utf-8", "cp1252"):
                try:
                    with sheet_path.open("r", encoding=encoding, newline="") as handle:
                        reader = csv.DictReader(handle)
                        headers = list(reader.fieldnames or [])
                        return headers, [dict(row) for row in reader]
                except UnicodeDecodeError as exc:
                    last_error = exc
            raise ValueError("The CSV file could not be decoded as UTF-8 or Windows-1252.") from last_error

        if suffix == ".xlsx":
            try:
                from openpyxl import load_workbook
            except ImportError as exc:
                raise ValueError("Excel import requires the 'openpyxl' package. Install it and try again.") from exc
            workbook = load_workbook(sheet_path, read_only=True, data_only=True)
            try:
                worksheet = workbook.active
                row_iterator = worksheet.iter_rows(values_only=True)
                raw_headers = next(row_iterator, None)
                if raw_headers is None:
                    return [], []
                headers = ["" if value is None else str(value).strip() for value in raw_headers]
                rows = [
                    {headers[index]: value for index, value in enumerate(row) if index < len(headers)}
                    for row in row_iterator
                    if any(value not in (None, "") for value in row)
                ]
                return headers, rows
            finally:
                workbook.close()

        if suffix == ".xls":
            try:
                import pandas as pd
            except ImportError as exc:
                raise ValueError("Legacy .xls import requires the 'pandas' and 'xlrd' packages. Use .csv or .xlsx instead.") from exc
            try:
                dataframe = pd.read_excel(sheet_path, dtype=str).fillna("")
            except Exception as exc:
                raise ValueError(f"Could not read the Excel file: {exc}") from exc
            headers = [str(column).strip() for column in dataframe.columns]
            return headers, [{str(key): value for key, value in row.items()} for row in dataframe.to_dict("records")]

        raise ValueError("Choose a CSV, XLSX, or XLS file.")

    @staticmethod
    def _metadata_columns_from_json(raw_data: object) -> list[str]:
        """Read a column template from either a JSON list or a metadata_columns object."""
        if isinstance(raw_data, list):
            values = raw_data
        elif isinstance(raw_data, dict):
            values = raw_data.get("metadata_columns", raw_data.get("columns"))
        else:
            values = None
        if not isinstance(values, list):
            raise ValueError(
                "JSON must be a list of column names or an object with a 'metadata_columns' or 'columns' list."
            )
        columns: list[str] = []
        seen: set[str] = set()
        for value in values:
            if not isinstance(value, str) or not value.strip():
                raise ValueError("Every metadata column name in JSON must be a non-empty string.")
            name = value.strip()
            key = name.casefold()
            if key not in seen:
                columns.append(name)
                seen.add(key)
        if not columns:
            raise ValueError("The JSON file does not contain any metadata column names.")
        return columns

    def load_metadata_columns_json(self) -> None:
        """Add empty metadata columns from JSON without changing loaded sheet values."""
        if not self.data_definition_files:
            QMessageBox.information(
                self,
                "Source Required",
                "Select a folder or file and wait for it to appear before loading metadata columns.",
            )
            return
        file_path, _ = QFileDialog.getOpenFileName(
            self,
            "Load Metadata Columns from JSON",
            "",
            "JSON Files (*.json);;All Files (*)",
        )
        if not file_path:
            return
        try:
            with Path(file_path).open("r", encoding="utf-8") as handle:
                columns = self._metadata_columns_from_json(json.load(handle))
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            QMessageBox.warning(self, "Metadata Columns Could Not Be Loaded", str(exc))
            return

        existing_keys = {column.casefold() for column in self.custom_business_metadata_columns}
        added_columns = [column for column in columns if column.casefold() not in existing_keys]
        self.custom_business_metadata_columns.extend(added_columns)
        self.populate_data_definition_table()
        self.add_log(
            f"Loaded {len(added_columns)} empty business metadata column(s) from JSON template "
            f"'{Path(file_path).name}'."
        )
        QMessageBox.information(
            self,
            "Metadata Columns Loaded",
            f"Added {len(added_columns)} empty metadata column(s). Existing metadata values were retained.",
        )

    def load_business_metadata_sheet(self) -> None:
        """Populate only existing config or manually added fields by File Name."""
        if not self.data_definition_files:
            QMessageBox.information(self, "Source Required", "Select a folder or file before loading a metadata sheet.")
            return
        if not self.custom_business_metadata_columns:
            QMessageBox.information(
                self,
                "Metadata Columns Required",
                "Load a config file with metadata_columns or add a manual metadata column before loading a sheet.",
            )
            return
        selected_path, _ = QFileDialog.getOpenFileName(
            self, "Load Business Metadata Sheet", "",
            "Metadata sheets (*.csv *.xlsx *.xls);;CSV files (*.csv);;Excel files (*.xlsx *.xls)",
        )
        if not selected_path:
            return
        try:
            headers, sheet_rows = self._read_business_metadata_sheet(Path(selected_path))
        except (OSError, ValueError) as exc:
            QMessageBox.warning(self, "Metadata Sheet Could Not Be Loaded", str(exc))
            return
        normalized_headers = {self._metadata_sheet_key(header): header for header in headers if str(header).strip()}
        file_name_header = normalized_headers.get("filename")
        if file_name_header is None:
            QMessageBox.warning(self, "Required Column Missing", "The metadata sheet must contain a 'File Name' column.")
            return

        existing_by_key = {column.casefold(): column for column in self.custom_business_metadata_columns}
        matching_columns = [
            existing_by_key[header.casefold()]
            for header in headers
            if header != file_name_header and str(header).strip() and header.casefold() in existing_by_key
        ]
        # Preserve sheet-to-app name mapping for case differences.
        sheet_header_for_column = {existing_by_key[header.casefold()]: header for header in headers if header != file_name_header and str(header).strip() and header.casefold() in existing_by_key}
        if not matching_columns:
            QMessageBox.information(
                self, "No Matching Metadata Columns",
                "No CSV/Excel metadata column matches the existing config or manual metadata columns. No columns were created.",
            )
            return

        prepared_files: dict[str, list[Path]] = {}
        for file_path in self.data_definition_files:
            prepared_files.setdefault(file_path.name.casefold(), []).append(file_path)
        matched_sheet_rows = 0
        populated_files: set[str] = set()
        for sheet_row in sheet_rows:
            file_name = str(sheet_row.get(file_name_header, "")).strip()
            matching_paths = prepared_files.get(file_name.casefold(), [])
            if not matching_paths:
                continue
            matched_sheet_rows += 1
            for file_path in matching_paths:
                values = self.custom_business_metadata_values.setdefault(str(file_path), {})
                for column in matching_columns:
                    raw_value = sheet_row.get(sheet_header_for_column[column], "")
                    values[column] = "" if raw_value is None else str(raw_value)
                populated_files.add(str(file_path))
        self.populate_data_definition_table()
        ignored_columns = len([header for header in headers if header != file_name_header and str(header).strip()]) - len(matching_columns)
        unmatched_rows = len(sheet_rows) - matched_sheet_rows
        self.add_log(f"Loaded metadata sheet '{Path(selected_path).name}': {len(matching_columns)} matching column(s), {ignored_columns} ignored column(s), {len(populated_files)} file(s) populated.")
        QMessageBox.information(
            self, "Business Metadata Loaded",
            f"Populated {len(matching_columns)} existing metadata column(s) for {len(populated_files)} prepared file(s). "
            f"{ignored_columns} sheet column(s) were ignored because they do not match an existing metadata column; no new columns were created. "
            f"{unmatched_rows} sheet row(s) did not match a prepared file name.",
        )

    def _rebuild_business_metadata_columns(self) -> None:
        """Combine locked config columns and optional manual columns without duplicates."""
        combined: list[str] = []
        seen: set[str] = set()
        for column in [
            *self.system_business_metadata_columns,
            *self.config_business_metadata_columns,
            *self.manual_business_metadata_columns,
        ]:
            if column.casefold() not in seen:
                combined.append(column)
                seen.add(column.casefold())
        self.custom_business_metadata_columns = combined

    def is_manual_business_metadata_column(self, column_name: str) -> bool:
        return column_name.casefold() in {column.casefold() for column in self.manual_business_metadata_columns}

    def add_custom_business_metadata_column(self) -> None:
        column_name, accepted = QInputDialog.getText(
            self,
            "Add Business Metadata Column",
            "Metadata field name:",
        )
        normalized_name = column_name.strip()
        if not accepted or not normalized_name:
            return
        if normalized_name.casefold() in {column.casefold() for column in self.custom_business_metadata_columns}:
            QMessageBox.information(self, "Duplicate Metadata Field", "That business metadata field already exists.")
            return
        self.manual_business_metadata_columns.append(normalized_name)
        self._rebuild_business_metadata_columns()
        self.populate_data_definition_table()

    def _store_custom_business_metadata_value(self, file_path: Path, column_name: str, value: str) -> None:
        file_values = self.custom_business_metadata_values.setdefault(str(file_path), {})
        file_values[column_name] = value

    def replicate_metadata_from_header(self, column_name: str) -> None:
        if len(self.data_definition_files) < 2:
            return
        first_file = self.data_definition_files[0]
        value = self.custom_business_metadata_values.get(str(first_file), {}).get(column_name, "").strip()
        if not value:
            QMessageBox.information(
                self,
                "First-Row Value Required",
                f"Enter a value for '{column_name}' in the first row before replicating it.",
            )
            return
        self.replicate_business_metadata_to_all(column_name)

    def on_data_definition_header_pressed(self, section: int) -> None:
        self.data_definition_header_pressed_position = self.data_definition_table.horizontalHeader().mapFromGlobal(QCursor.pos())

    def on_data_definition_header_clicked(self, section: int) -> None:
        metadata_start_column = 4
        metadata_end_column = metadata_start_column + len(self.custom_business_metadata_columns)
        if not (metadata_start_column <= section < metadata_end_column):
            return
        column_name = self.custom_business_metadata_columns[section - metadata_start_column]
        header = self.data_definition_table.horizontalHeader()
        section_rect = QRect(header.sectionViewportPosition(section), 0, header.sectionSize(section), header.height())
        pressed_position = getattr(self, "data_definition_header_pressed_position", None)
        if (
            self.is_manual_business_metadata_column(column_name)
            and pressed_position is not None
            and pressed_position.x() >= section_rect.right() - 24
        ):
            self.remove_custom_business_metadata_column(column_name)
            return
        if self.archive_source_mode.currentData() != "folder" or len(self.data_definition_files) < 2:
            return
        first_file = self.data_definition_files[0]
        value = self.custom_business_metadata_values.get(str(first_file), {}).get(column_name, "").strip()
        if not value:
            QMessageBox.information(
                self,
                "First-Row Value Required",
                f"Enter a value for '{column_name}' in the first row before replicating it.",
            )
            return
        self.replicate_business_metadata_to_all(column_name)

    def remove_custom_business_metadata_column(self, column_name: str) -> None:
        if not self.is_manual_business_metadata_column(column_name):
            return
        self.manual_business_metadata_columns = [
            column for column in self.manual_business_metadata_columns
            if column.casefold() != column_name.casefold()
        ]
        self._rebuild_business_metadata_columns()
        for values in self.custom_business_metadata_values.values():
            values.pop(column_name, None)
        self.populate_data_definition_table()

    def replicate_business_metadata_to_all(self, column_name: str) -> None:
        if not self.data_definition_files:
            return
        first_file = self.data_definition_files[0]
        value = self.custom_business_metadata_values.get(str(first_file), {}).get(column_name, "").strip()
        if not value:
            return
        for file_path in self.data_definition_files:
            self.custom_business_metadata_values.setdefault(str(file_path), {})[column_name] = value
        self.populate_data_definition_table()
        self.add_log(f"Replicated business metadata field '{column_name}' to all prepared files.")

    def _apply_data_definition_column_widths(self) -> None:
        """Keep the table readable and enable horizontal scrolling for many metadata fields."""
        table = self.data_definition_table
        header = table.horizontalHeader()
        metadata_count = len(self.custom_business_metadata_columns)
        use_horizontal_scroll = metadata_count >= 3
        header.setStretchLastSection(False)
        header.setMinimumSectionSize(50)

        action_column = 0
        file_name_column = 1
        full_path_column = 2
        size_column = 3
        metadata_start_column = 4

        header.setSectionResizeMode(action_column, QHeaderView.Fixed)
        table.setColumnWidth(action_column, 90)
        header.setSectionResizeMode(file_name_column, QHeaderView.Fixed)
        table.setColumnWidth(file_name_column, 200)
        header.setSectionResizeMode(size_column, QHeaderView.Fixed)
        table.setColumnWidth(size_column, 110)

        # With three or more metadata columns, retain useful widths for every
        # field and expose a horizontal scrollbar instead of compressing them.
        if use_horizontal_scroll:
            header.setSectionResizeMode(full_path_column, QHeaderView.Fixed)
            table.setColumnWidth(full_path_column, 400)
            table.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOn)
        else:
            header.setSectionResizeMode(full_path_column, QHeaderView.Stretch)
            table.setHorizontalScrollBarPolicy(Qt.ScrollBarAsNeeded)

        metadata_width = 250 if use_horizontal_scroll else 150
        for column in range(metadata_start_column, table.columnCount()):
            header.setSectionResizeMode(column, QHeaderView.Interactive)
            table.setColumnWidth(column, max(metadata_width, table.columnWidth(column)))

    def populate_data_definition_table(self) -> None:
        self.data_definition_table.setRowCount(0)
        headers = ["Action", "File Name", "Full Path", "Size", *self.custom_business_metadata_columns]
        self.data_definition_table.setColumnCount(len(headers))
        self.data_definition_table.setHorizontalHeaderLabels(headers)
        self._apply_data_definition_column_widths()

        action_column = 0
        file_name_column = 1
        full_path_column = 2
        size_column = 3
        metadata_start_column = 4
        for offset, column_name in enumerate(self.custom_business_metadata_columns):
            header_item = self.data_definition_table.horizontalHeaderItem(metadata_start_column + offset)
            if header_item is not None:
                header_item.setText(column_name)
                is_folder_source = self.archive_source_mode.currentData() == "folder"
                is_system = column_name == WINDOWS_USER_METADATA_COLUMN
                is_manual = self.is_manual_business_metadata_column(column_name)
                if is_system:
                    header_item.setToolTip("Automatically detected Windows user name. This required metadata cannot be removed.")
                elif is_folder_source and is_manual:
                    header_item.setToolTip("Click the replicate icon to copy the first-row value; click the remove icon to delete this manual column.")
                elif is_folder_source:
                    header_item.setToolTip("Config-required metadata column. Click the replicate icon to copy the first-row value.")
                elif is_manual:
                    header_item.setToolTip("Click the remove icon to delete this manual column.")
                else:
                    header_item.setToolTip("Config-required metadata column.")
        root_folder = self.data_definition_root_folder
        for row, file_path in enumerate(self.data_definition_files):
            self.data_definition_table.insertRow(row)
            full_path = str(file_path.resolve())
            for column, value in (
                (file_name_column, file_path.name),
                (full_path_column, full_path),
                (size_column, format_size(file_path.stat().st_size)),
            ):
                item = QTableWidgetItem(value)
                item.setTextAlignment(Qt.AlignCenter)
                if column == full_path_column:
                    item.setToolTip(full_path)
                self.data_definition_table.setItem(row, column, item)
            saved_values = self.custom_business_metadata_values.get(str(file_path), {})
            for offset, column_name in enumerate(self.custom_business_metadata_columns):
                value_input = QLineEdit(saved_values.get(column_name, ""))
                value_input.setPlaceholderText(f"Enter {column_name}")
                if column_name == WINDOWS_USER_METADATA_COLUMN:
                    value_input.setReadOnly(True)
                    value_input.setToolTip("Automatically detected logged-in Windows user. This Archive Uploader metadata is sent with every archive.")
                else:
                    value_input.textChanged.connect(
                        partial(self._store_custom_business_metadata_value, file_path, column_name)
                    )
                metadata_column = metadata_start_column + offset
                self.data_definition_table.setCellWidget(row, metadata_column, value_input)
            remove_button = SvgActionButton(
                "bin.svg",
                tooltip="Remove file from transfer list",
                accessible_name="Remove file",
                fallback_text="×",
            )
            remove_button.clicked.connect(partial(self.remove_data_definition_file, file_path))
            action_container = QWidget()
            action_layout = QHBoxLayout(action_container)
            action_layout.setContentsMargins(0, 0, 0, 0)
            action_layout.setAlignment(Qt.AlignCenter)
            action_layout.addWidget(remove_button)
            self.data_definition_table.setCellWidget(row, action_column, action_container)

    def remove_data_definition_file(self, file_path: Path) -> None:
        self.data_definition_files = [path for path in self.data_definition_files if path != file_path]
        self.custom_business_metadata_values.pop(str(file_path), None)
        self.populate_data_definition_table()

    def move_data_definition_to_transfers(self) -> None:
        if not self._is_current_user_authorized():
            QMessageBox.critical(
                self,
                "You Are Not Authorized",
                "You are not authorized to Archive Files for this application. "
                "Ask archival support to get access and your Config ZIP.",
            )
            return
        if self.is_worker_running():
            QMessageBox.information(self, "Busy", "Wait for the active archive run to finish before changing the transfer list.")
            return
        if not self.data_definition_files or self.data_definition_root_folder is None:
            QMessageBox.information(self, "No Data Defined", "Select a source and keep at least one file before moving data to Transfers.")
            return

        choice_dialog = QDialog(self)
        choice_dialog.setWindowTitle("Prepare Transfer")
        choice_dialog.setModal(True)
        choice_dialog.setMinimumWidth(500)
        layout = QVBoxLayout(choice_dialog)
        message = QLabel(
            "Choose how to prepare the currently selected files for transfer. "
            "Creating a ZIP leaves the original files unchanged and sends one ZIP file to Transfers."
        )
        message.setWordWrap(True)
        layout.addWidget(message)

        zip_button = QPushButton("Zip Selected Files and Move to Transfers")
        zip_button.setObjectName("secondaryActionButton")
        all_files_button = QPushButton("Move All Files to Transfers")
        cancel_button = QPushButton("Cancel")
        layout.addWidget(zip_button)
        layout.addWidget(all_files_button)
        layout.addWidget(cancel_button, 0, Qt.AlignRight)

        selected_option: dict[str, str | None] = {"value": None}
        zip_button.clicked.connect(lambda: (selected_option.__setitem__("value", "zip"), choice_dialog.accept()))
        all_files_button.clicked.connect(lambda: (selected_option.__setitem__("value", "all"), choice_dialog.accept()))
        cancel_button.clicked.connect(choice_dialog.reject)
        if choice_dialog.exec() != QDialog.Accepted or selected_option["value"] is None:
            return

        zip_source_files: tuple[Path, ...] = ()
        zip_source_root: Path | None = None
        if selected_option["value"] == "zip":
            # The archive ZIP is created in app storage. On successful archival,
            # its original source files are moved to <source>/Zip Outbound.
            zip_directory = app_storage_dir() / "prepared_transfer_zips"
            zip_directory.mkdir(parents=True, exist_ok=True)
            zip_source_files = tuple(self.data_definition_files)
            zip_source_root = self.data_definition_root_folder
            default_zip_stem = f"transfer_{datetime.now().strftime('%Y%m%d_%H%M%S_%f')}"
            temporary_zip_path = zip_directory / f".{default_zip_stem}.creating.zip"
            total_files = len(self.data_definition_files)
            total_size = sum(file_path.stat().st_size for file_path in self.data_definition_files)

            progress_dialog = QDialog(self)
            progress_dialog.setWindowTitle("Creating Transfer ZIP")
            progress_dialog.setModal(True)
            progress_dialog.setWindowFlags(progress_dialog.windowFlags() & ~Qt.WindowCloseButtonHint)
            progress_dialog.setMinimumWidth(520)
            progress_layout = QVBoxLayout(progress_dialog)
            progress_title = QLabel("Creating ZIP for transfer")
            progress_title.setObjectName("folderLoadingTitle")
            progress_message = QLabel(
                f"Preparing {total_files} file(s) ({format_size(total_size)}) for transfer."
            )
            progress_message.setWordWrap(True)
            progress_detail = QLabel("Starting...")
            progress_detail.setObjectName("refreshLabel")
            progress_detail.setWordWrap(True)
            progress_bar = QProgressBar()
            progress_bar.setRange(0, total_files)
            progress_bar.setValue(0)
            progress_layout.addWidget(progress_title)
            progress_layout.addWidget(progress_message)
            progress_layout.addWidget(progress_detail)
            progress_layout.addWidget(progress_bar)
            progress_dialog.show()
            QApplication.processEvents()

            try:
                with zipfile.ZipFile(temporary_zip_path, "w", zipfile.ZIP_DEFLATED) as archive:
                    for index, file_path in enumerate(self.data_definition_files, start=1):
                        progress_detail.setText(f"Adding file {index} of {total_files}: {file_path.name}")
                        progress_bar.setValue(index - 1)
                        QApplication.processEvents()
                        archive.write(file_path, arcname=str(file_path.relative_to(self.data_definition_root_folder)))
                        progress_bar.setValue(index)
                        QApplication.processEvents()
            except (OSError, ValueError, zipfile.BadZipFile) as exc:
                progress_dialog.close()
                if temporary_zip_path.exists():
                    temporary_zip_path.unlink()
                QMessageBox.critical(self, "ZIP Creation Failed", f"The transfer ZIP could not be created.\n{exc}")
                return

            progress_dialog.setWindowTitle("Name Transfer ZIP")
            progress_title.setText("ZIP creation complete")
            progress_message.setText("Enter the ZIP file name before moving it to Transfers.")
            progress_detail.setText(f"Created {total_files} file(s), totaling {format_size(total_size)}.")
            zip_name_label = QLabel("ZIP file name")
            zip_name_input = QLineEdit(default_zip_stem)
            zip_name_input.setPlaceholderText("Enter ZIP file name")
            zip_name_input.setToolTip("The .zip extension is added automatically.")
            name_hint = QLabel(
                "The .zip extension is added automatically. After successful archival, the original source files move to the source folder's Zip Outbound folder."
            )
            name_hint.setObjectName("refreshLabel")
            name_hint.setWordWrap(True)
            complete_button = QPushButton("Move ZIP to Transfers")
            complete_button.setObjectName("secondaryActionButton")
            cancel_button = QPushButton("Cancel")
            buttons_layout = QHBoxLayout()
            buttons_layout.addStretch()
            buttons_layout.addWidget(cancel_button)
            buttons_layout.addWidget(complete_button)
            progress_layout.addWidget(zip_name_label)
            progress_layout.addWidget(zip_name_input)
            progress_layout.addWidget(name_hint)
            progress_layout.addLayout(buttons_layout)
            zip_name_input.setFocus()
            zip_name_input.selectAll()

            naming_accepted = {"value": False}
            complete_button.clicked.connect(lambda: (naming_accepted.__setitem__("value", True), progress_dialog.accept()))
            cancel_button.clicked.connect(progress_dialog.reject)
            if progress_dialog.exec() != QDialog.Accepted or not naming_accepted["value"]:
                if temporary_zip_path.exists():
                    temporary_zip_path.unlink()
                return

            zip_stem = zip_name_input.text().strip()
            invalid_characters = '<>:"/\\|?*'
            if not zip_stem or zip_stem != Path(zip_stem).name or any(character in zip_stem for character in invalid_characters):
                if temporary_zip_path.exists():
                    temporary_zip_path.unlink()
                QMessageBox.warning(
                    self,
                    "Invalid ZIP Name",
                    "Enter a ZIP name without folders or these characters: < > : \" / \\ | ? *",
                )
                return
            if zip_stem.casefold().endswith(".zip"):
                zip_stem = zip_stem[:-4]
            if not zip_stem:
                if temporary_zip_path.exists():
                    temporary_zip_path.unlink()
                QMessageBox.warning(self, "Invalid ZIP Name", "Enter a ZIP file name before moving it to Transfers.")
                return
            zip_name = f"{zip_stem}.zip"
            zip_path = zip_directory / zip_name
            if zip_path.exists():
                if temporary_zip_path.exists():
                    temporary_zip_path.unlink()
                QMessageBox.warning(self, "ZIP Name Already Exists", f"A ZIP named '{zip_name}' already exists. Choose a different name.")
                return
            try:
                temporary_zip_path.rename(zip_path)
            except OSError as exc:
                if temporary_zip_path.exists():
                    temporary_zip_path.unlink()
                QMessageBox.critical(self, "ZIP Rename Failed", f"The transfer ZIP could not be named.\n{exc}")
                return

            files_to_transfer = [zip_path]
            transfer_root = zip_directory
            metadata_by_path = {str(zip_path): {WINDOWS_USER_METADATA_COLUMN: self.windows_user_name}}
            log_message = (
                f"Created transfer ZIP '{zip_name}' from {len(self.data_definition_files)} prepared file(s) "
                "and moved it to Transfers."
            )
        else:
            files_to_transfer = list(self.data_definition_files)
            transfer_root = self.data_definition_root_folder
            metadata_by_path = self.custom_business_metadata_values
            log_message = f"Moved {len(files_to_transfer)} prepared file(s) to Transfers and cleared the Data Definition table."

        self.root_folder = transfer_root
        self.current_run_id = None
        self.tasks = []
        self.moved_task_rows.clear()
        self.table.setRowCount(0)
        self.overall_progress.setValue(0)
        for row, file_path in enumerate(files_to_transfer):
            relative_path = str(file_path.relative_to(self.root_folder))
            task = ArchiveTask(
                row=row,
                file_path=file_path,
                relative_path=relative_path,
                size_bytes=file_path.stat().st_size,
                full_path=str(file_path.resolve()),
                file_name=file_path.name,
                custom_business_metadata=dict(metadata_by_path.get(str(file_path), {})),
                is_transfer_zip=selected_option["value"] == "zip",
                zip_source_files=zip_source_files if selected_option["value"] == "zip" else (),
                zip_source_root=zip_source_root if selected_option["value"] == "zip" else None,
            )
            self.tasks.append(task)
            self._insert_task_row(task)
        self.data_definition_files = []
        self.data_definition_root_folder = None
        self.manual_business_metadata_columns = []
        self._rebuild_business_metadata_columns()
        self.custom_business_metadata_values = {}
        self.folder_input.clear()
        self.populate_data_definition_table()
        self._update_metadata_sheet_button_visibility()
        self.update_summary_cards()
        self._update_refresh_timestamp()
        self.tabs.setCurrentWidget(self.transfer_tab)
        self.add_log(log_message)

    def _insert_task_row(self, task: ArchiveTask) -> None:
        self._insert_task_row_at(self.table.rowCount(), task)

    def _insert_task_row_at(self, display_row: int, task: ArchiveTask) -> None:
        self.table.insertRow(display_row)
        for column, value in enumerate([task.relative_path, format_size(task.size_bytes), task.task_id]):
            table_item = QTableWidgetItem(value)
            table_item.setTextAlignment(Qt.AlignCenter)
            self.table.setItem(display_row, column, table_item)

        progress_bar = QProgressBar()
        progress_bar.setValue(task.progress)
        self.table.setCellWidget(display_row, 3, progress_bar)
        status_item = QTableWidgetItem(task.status)
        status_item.setTextAlignment(Qt.AlignCenter)
        self._apply_transfer_status_style(status_item, task.status)
        self.table.setItem(display_row, 4, status_item)
        self.table.setCellWidget(display_row, 5, self._create_row_action_widget(display_row))

    def _create_row_action_widget(self, row: int) -> QWidget:
        widget = QWidget()
        layout = QHBoxLayout(widget)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        start_btn = SvgActionButton(
            "start.svg", tooltip="Start task", accessible_name="Start task", fallback_text="▶"
        )
        start_btn.clicked.connect(partial(self.start_selected_tasks, [row]))

        stop_btn = SvgActionButton(
            "stop.svg", tooltip="Stop task", accessible_name="Stop task", fallback_text="■"
        )
        stop_btn.clicked.connect(partial(self.stop_selected_tasks, [row]))

        cancel_btn = SvgActionButton(
            "cancel.svg", tooltip="Cancel task", accessible_name="Cancel task", fallback_text="×"
        )
        cancel_btn.clicked.connect(partial(self.cancel_selected_tasks, [row]))

        retry_btn = SvgActionButton(
            "re-start.svg", tooltip="Retry failed task", accessible_name="Retry failed task", fallback_text="↻"
        )
        retry_btn.clicked.connect(partial(self.retry_failed_tasks, [row]))

        layout.addWidget(start_btn)
        layout.addWidget(stop_btn)
        layout.addWidget(cancel_btn)
        layout.addWidget(retry_btn)
        return widget

    def _set_archive_starting_state(self, active: bool, message: str = "") -> None:
        """Show immediate feedback while archive startup work is being prepared."""
        if active:
            self.archive_starting_banner.setText(
                message or "Preparing archive run. Please wait — archival startup is in progress."
            )
            self.archive_starting_banner.setVisible(True)
            self.start_btn.setEnabled(False)
            self.start_btn.setText("Preparing Archive...")
            QApplication.processEvents()
            return
        self.archive_starting_banner.setVisible(False)
        self.start_btn.setEnabled(True)
        self.start_btn.setText("Start Archiving")

    def start_processing(self) -> None:
        if self.root_folder is None or not self.tasks:
            QMessageBox.information(self, "Data Definition Required", "Prepare and move one or more files from the Data Definition page before starting archival.")
            self.tabs.setCurrentWidget(self.data_definition_tab)
            return

        self._set_archive_starting_state(True, "Preparing selected files and starting archival. Please wait...")
        ready_count = self._mark_all_startable_ready()
        if ready_count == 0:
            self._set_archive_starting_state(False)
            self.add_log("No queued tasks were available to start. Mark files as Stopped before the run to skip them for now.")
            return

        if self.check_connectivity():
            self.add_log(f"Marked {ready_count} task(s) as Ready.")
            if self.ensure_worker_running():
                self.archive_starting_banner.setText("Archive worker is running. Files will begin uploading shortly.")
                self.add_log("Archive worker started.")
            else:
                self._set_archive_starting_state(False)
        else:
            self._wait_for_network([task.row for task in self.tasks if task.status == "Ready"])
            self.archive_starting_banner.setText("Archive is ready but waiting for network connectivity.")

    def _wait_for_network(self, rows: list[int]) -> None:
        changed_rows: list[int] = []
        with self.task_lock:
            for row in rows:
                if not (0 <= row < len(self.tasks)):
                    continue
                task = self.tasks[row]
                if task.status == "Ready":
                    task.status = WAITING_FOR_NETWORK_STATUS
                    changed_rows.append(row)
        for row in changed_rows:
            self.refresh_row(row)
        if changed_rows:
            self.waiting_for_network = True
            self.add_log("Network is offline. Selected archive tasks are waiting for network connectivity.")

    def _resume_waiting_for_network_tasks(self) -> None:
        with self.task_lock:
            waiting_rows = [task.row for task in self.tasks if task.status == WAITING_FOR_NETWORK_STATUS]
            for row in waiting_rows:
                self.tasks[row].status = "Ready"
        for row in waiting_rows:
            self.refresh_row(row)
        self.waiting_for_network = False
        if not waiting_rows:
            return
        self.add_log("Network is live. Resuming waiting archive tasks.")
        if hasattr(self, "archive_starting_banner") and self.archive_starting_banner.isVisible():
            self.archive_starting_banner.setText("Network restored. Archive processing is resuming.")
        # If a worker is processing another task it will pick these Ready rows;
        # otherwise start a worker immediately.
        if not self.is_worker_running() and self.ensure_worker_running():
            self.add_log("Archive worker started after network recovery.")

    def _mark_all_startable_ready(self) -> int:
        ready_count = 0
        with self.task_lock:
            for task in self.tasks:
                if task.status in STARTABLE_STATUSES:
                    task.status = "Ready"
                    # Keep remote task id, idempotency keys, commit state, and part checkpoints.
                    # Retry will reconcile the existing remote upload instead of creating another.
                    task.progress = 0
                    task.archived_at = "-"
                    task.stop_requested = False
                    task.cancel_requested = False
                    ready_count += 1
        for task in self.tasks:
            if task.status == "Ready":
                self.refresh_row(task.row)
        self.recalculate_overall_progress()
        return ready_count

    def show_task_context_menu(self, position: QPoint) -> None:
        selected_rows = self.selected_rows()
        if not selected_rows:
            return

        statuses = {self.tasks[row].status for row in selected_rows if 0 <= row < len(self.tasks)}
        menu = QMenu(self)
        start_action = menu.addAction("Start Selected")
        stop_action = menu.addAction("Stop Selected")
        cancel_action = menu.addAction("Cancel Selected")
        retry_action = menu.addAction("Retry Failed")

        start_action.setEnabled(any(status in STARTABLE_STATUSES for status in statuses))
        stop_action.setEnabled(any(status in STOPPABLE_STATUSES for status in statuses))
        cancel_action.setEnabled(any(status in CANCELABLE_STATUSES for status in statuses))
        retry_action.setEnabled(any(status in RETRYABLE_STATUSES for status in statuses))

        chosen_action = menu.exec(self.table.viewport().mapToGlobal(position))
        if chosen_action is start_action:
            self.start_selected_tasks(selected_rows)
        elif chosen_action is stop_action:
            self.stop_selected_tasks(selected_rows)
        elif chosen_action is cancel_action:
            self.cancel_selected_tasks(selected_rows)
        elif chosen_action is retry_action:
            self.retry_failed_tasks(selected_rows)

    def _task_index_for_run_row(self, run_row: int) -> int | None:
        """Find the current list position for a task's immutable archive run row."""
        for index, task in enumerate(self.tasks):
            if task.row == run_row:
                return index
        return None

    def start_selected_tasks(self, rows: list[int]) -> None:
        if not self._prepare_worker_environment():
            return
        changed = 0
        with self.task_lock:
            for row in rows:
                if not (0 <= row < len(self.tasks)):
                    continue
                task = self.tasks[row]
                if task.status in MANUALLY_STARTABLE_STATUSES:
                    task.status = "Ready"
                    task.progress = 0
                    task.task_id = "-"
                    task.archived_at = "-"
                    task.stop_requested = False
                    task.cancel_requested = False
                    changed += 1
        for row in rows:
            self.refresh_row(row)
        if changed == 0:
            self.add_log("Start action ignored because no selected task was queued or stopped.")
            return
        if self.check_connectivity():
            self.add_log(f"Marked {changed} selected task(s) as Ready.")
            if self.ensure_worker_running():
                self.add_log("Archive worker started.")
        else:
            self._wait_for_network(rows)

    def stop_selected_tasks(self, rows: list[int]) -> None:
        changed = 0
        with self.task_lock:
            for row in rows:
                if not (0 <= row < len(self.tasks)):
                    continue
                task = self.tasks[row]
                if task.status == "Queued":
                    task.status = "Stopped"
                    task.progress = 0
                    task.task_id = "-"
                    changed += 1
                elif task.status in {"Ready", WAITING_FOR_NETWORK_STATUS}:
                    task.status = "Stopped"
                    task.stop_requested = False
                    changed += 1
                elif task.status in {"Preparing", "Uploading"}:
                    task.stop_requested = True
                    # Show acknowledgement immediately; the worker will safely
                    # stop after the in-flight request returns or times out.
                    task.status = "Stopping"
                    changed += 1
        for row in rows:
            self.refresh_row(row)
        if changed:
            self.add_log(f"Stop requested for {changed} selected task(s).")
            self.recalculate_overall_progress()
        else:
            self.add_log("Stop action ignored because no selected task was active.")

    def cancel_selected_tasks(self, rows: list[int]) -> None:
        changed = 0
        active_cancel_rows: list[int] = []
        with self.task_lock:
            for row in rows:
                if not (0 <= row < len(self.tasks)):
                    continue
                task = self.tasks[row]
                if task.status in {"Queued", "Ready", "Stopped", "Failed", WAITING_FOR_NETWORK_STATUS}:
                    task.status = "Canceled"
                    task.progress = 0
                    task.task_id = "-"
                    task.archived_at = "-"
                    task.stop_requested = False
                    task.cancel_requested = False
                    changed += 1
                elif task.status in {"Preparing", "Uploading", "Stopping"}:
                    task.cancel_requested = True
                    task.status = "Canceling"
                    active_cancel_rows.append(row)
                    changed += 1
        # Inactive cancellations are immediately removed from the Transfers grid.
        # Active requests remain visible only until the request returns and safe
        # protocol cancellation is applied by the worker.
        inactive_rows = [row for row in rows if row not in active_cancel_rows]
        for row in inactive_rows:
            self.refresh_row(row)
        if inactive_rows:
            self._remove_canceled_transfer_rows()
        for row in active_cancel_rows:
            self.refresh_row(row)
        if changed:
            self.add_log(f"Cancel requested for {changed} selected task(s).")
            self.recalculate_overall_progress()
        else:
            self.add_log("Cancel action ignored because no selected task could be canceled.")

    def _remove_canceled_transfer_rows(self) -> None:
        """Remove canceled tasks from the visible Transfers table without renumbering run rows."""
        retained_tasks = [task for task in self.tasks if task.status != "Canceled"]
        self.table.setRowCount(0)
        self.tasks = retained_tasks
        for display_row, task in enumerate(self.tasks):
            # task.row stays its original archive run row_index for database continuity.
            self._insert_task_row_at(display_row, task)
        self.load_history_tables()
        self.refresh_analytics_panel()

    def retry_failed_tasks(self, rows: list[int]) -> None:
        if not self._prepare_worker_environment():
            return
        changed = 0
        with self.task_lock:
            for row in rows:
                if not (0 <= row < len(self.tasks)):
                    continue
                task = self.tasks[row]
                if task.status in RETRYABLE_STATUSES:
                    # Preserve task_id, idempotency keys, commit state, and part rows so
                    # the worker resumes/reconciles the original remote upload.
                    task.status = "Ready"
                    task.progress = 0
                    task.archived_at = "-"
                    task.stop_requested = False
                    task.cancel_requested = False
                    changed += 1
        for row in rows:
            self.refresh_row(row)
        if changed == 0:
            self.add_log("Retry action ignored because no selected task was failed.")
            return
        self.add_log(f"Retry requested for {changed} failed task(s).")
        if self.ensure_worker_running():
            self.add_log("Archive worker started.")

    def selected_rows(self) -> list[int]:
        selection_model = self.table.selectionModel()
        if selection_model is None:
            return []
        return sorted({index.row() for index in selection_model.selectedRows()})

    def on_task_progress_updated(self, row: int, percent: int, status: str) -> None:
        if status == WAITING_FOR_NETWORK_STATUS:
            self.waiting_for_network = True
        self.update_table_row(row, percent, status)
        task_index = self._task_index_for_run_row(row)
        if task_index is not None and status in {"Completed", "Canceled"}:
            self.post_process_task_file(self.tasks[task_index])
        self.persist_task_state(row)
        self.update_summary_cards()
        self.load_history_tables()
        self._update_refresh_timestamp()

    def update_table_row(self, row: int, percent: int, status: str) -> None:
        display_row = self._task_index_for_run_row(row)
        if display_row is None:
            return
        progress_bar = self.table.cellWidget(display_row, 3)
        if isinstance(progress_bar, QProgressBar):
            progress_bar.setValue(percent)
        status_item = self.table.item(display_row, 4)
        if status_item is not None:
            status_item.setText(status)
            self._apply_transfer_status_style(status_item, status)

    def _apply_transfer_status_style(self, item: QTableWidgetItem, status: str) -> None:
        if status == WAITING_FOR_NETWORK_STATUS:
            item.setForeground(QColor("#7b61ff"))
            item.setBackground(QColor("#f5f0ff"))
        elif status == "Stopped":
            item.setForeground(QColor("#d49a00"))
            item.setBackground(QColor("#fff9e6"))
        elif status == "Canceled":
            item.setForeground(QColor("#e1525c"))
            item.setBackground(QColor("#fff1f2"))
        else:
            item.setForeground(QColor("#0b1437"))
            item.setBackground(QColor("#ffffff"))

    def update_task_id(self, row: int, task_id: str) -> None:
        display_row = self._task_index_for_run_row(row)
        task_item = self.table.item(display_row, 2) if display_row is not None else None
        if task_item is not None:
            task_item.setText(task_id)
        self.persist_task_state(row)
        self.load_history_tables()

    def move_task_file(self, task: ArchiveTask, destination_folder_name: str) -> None:
        if self.root_folder is None:
            return
        source_path = task.file_path
        if not source_path.exists() or not source_path.is_file():
            task.full_path = str(source_path)
            return

        destination_root = self.root_folder / destination_folder_name
        destination_path = destination_root / task.relative_path
        destination_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(source_path), str(destination_path))
        task.file_path = destination_path
        task.full_path = str(destination_path.resolve())
        task.file_name = destination_path.name

    def post_process_task_file(self, task: ArchiveTask) -> None:
        if task.row in self.moved_task_rows:
            return
        try:
            if task.status == "Completed" and task.is_transfer_zip:
                moved_count = 0
                skipped_count = 0
                for source_path in task.zip_source_files:
                    if not source_path.exists() or not source_path.is_file():
                        skipped_count += 1
                        continue
                    try:
                        relative_path = source_path.relative_to(task.zip_source_root or source_path.parent)
                    except ValueError:
                        relative_path = Path(source_path.name)
                    destination_path = (task.zip_source_root or source_path.parent) / "Zip Outbound" / relative_path
                    destination_path.parent.mkdir(parents=True, exist_ok=True)
                    shutil.move(str(source_path), str(destination_path))
                    moved_count += 1
                self.moved_task_rows.add(task.row)
                self.add_log(
                    f"ZIP archive completed. Moved {moved_count} original source file(s) to Zip Outbound"
                    f"{f'; {skipped_count} file(s) were unavailable' if skipped_count else ''}."
                )
            elif task.status == "Completed":
                self.move_task_file(task, "Outbound")
                self.moved_task_rows.add(task.row)
                self.add_log(f"Moved archived file to Outbound: {task.relative_path}")
            elif task.status == "Canceled":
                self.move_task_file(task, "Cancelled")
                self.moved_task_rows.add(task.row)
                self.add_log(f"Moved canceled file to Cancelled: {task.relative_path}")
        except Exception as exc:  # noqa: BLE001
            self.add_log(f"Unable to move file for {task.relative_path}: {exc}")

    def refresh_row(self, row: int) -> None:
        task_index = self._task_index_for_run_row(row)
        # UI actions may pass a current display index; worker signals pass an
        # immutable archive run row. Accept either without changing task.row.
        if task_index is None and 0 <= row < len(self.tasks):
            task_index = row
        if task_index is None:
            return
        task = self.tasks[task_index]
        self.update_table_row(task.row, task.progress, task.status)
        self.update_task_id(task.row, task.task_id)
        self.persist_task_state(task.row)
        self.update_summary_cards()
        self.load_history_tables()
        self._update_refresh_timestamp()

    def refresh_monitor(self) -> None:
        self.update_summary_cards()
        self.recalculate_overall_progress()
        self.load_history_tables()
        self.update_live_status(log_result=True)
        self._update_refresh_timestamp()
        self.add_log("Dashboard refreshed.")

    def auto_refresh_status(self) -> None:
        self.update_summary_cards()
        self.recalculate_overall_progress()
        self.load_history_tables()
        self.update_live_status(log_result=False)
        self._update_refresh_timestamp()

    def update_live_status(self, *, log_result: bool) -> None:
        """Request a background connectivity probe; never block the GUI event loop."""
        del log_result
        self._begin_connectivity_check()

    def _begin_connectivity_check(self) -> None:
        if self._connectivity_check_in_progress:
            return
        url = self.archive_service_url_input.text().strip() or self.auth_server_input.text().strip()
        proxy_url = self.proxy_url_input.text().strip()
        proxy_enabled = self.proxy_toggle_btn.isChecked()
        self._connectivity_check_in_progress = True

        def probe() -> None:
            if not url:
                self.connectivity_result.emit(False)
                return
            proxies = {"http": proxy_url, "https": proxy_url} if proxy_enabled and proxy_url else None
            try:
                session = requests.Session()
                session.trust_env = False
                response = session.get(url, timeout=(1, 2), proxies=proxies, verify=True)
                self.connectivity_result.emit(response.status_code < 500)
            except RequestException:
                self.connectivity_result.emit(False)

        threading.Thread(target=probe, name="archive-connectivity-probe", daemon=True).start()

    def _on_connectivity_result(self, is_online: bool) -> None:
        self._connectivity_check_in_progress = False
        if is_online:
            self.live_badge.setText("Live")
            self.live_badge.setObjectName("liveBadge")
            self._resume_waiting_for_network_tasks()
        else:
            self.live_badge.setText("Offline")
            self.live_badge.setObjectName("offlineBadge")
            if self.is_worker_running():
                self._wait_for_network([task.row for task in self.tasks if task.status == "Ready"])
                if hasattr(self, "archive_starting_banner"):
                    self.archive_starting_banner.setText(
                        "Network connection lost. The current request will pause safely; remaining files are waiting for network recovery."
                    )
                    self.archive_starting_banner.setVisible(True)
        self.live_badge.style().unpolish(self.live_badge)
        self.live_badge.style().polish(self.live_badge)
        self.live_badge.update()

    def check_connectivity(self) -> bool:
        """Fast startup probe only; recurring monitoring uses the background probe."""
        url = self.archive_service_url_input.text().strip() or self.auth_server_input.text().strip()
        if not url:
            return False
        proxy_url = self.proxy_url_input.text().strip()
        proxies = {"http": proxy_url, "https": proxy_url} if self.proxy_toggle_btn.isChecked() and proxy_url else None
        try:
            session = requests.Session()
            session.trust_env = False
            response = session.get(url, timeout=(0.5, 1), proxies=proxies, verify=True)
            return response.status_code < 500
        except RequestException:
            return False

    def _set_proxy_environment(self, enabled: bool) -> None:
        proxy_variable_names = ("HTTP_PROXY", "HTTPS_PROXY", "http_proxy", "https_proxy")
        no_proxy_variable_names = ("NO_PROXY", "no_proxy")

        if enabled:
            proxy_url = self.proxy_url_input.text().strip()
            if not proxy_url:
                raise ValueError("Enter a Proxy URL in Settings before enabling the proxy.")
            for variable_name in (*proxy_variable_names, *no_proxy_variable_names):
                if variable_name not in self._proxy_environment_previous:
                    self._proxy_environment_previous[variable_name] = os.environ.get(variable_name)
            os.environ["NO_PROXY"] = "localhost,127.0.0.1"
            os.environ["no_proxy"] = "localhost,127.0.0.1"
            for variable_name in proxy_variable_names:
                os.environ[variable_name] = proxy_url
            return

        for variable_name, previous_value in self._proxy_environment_previous.items():
            if previous_value is None:
                os.environ.pop(variable_name, None)
            else:
                os.environ[variable_name] = previous_value
        self._proxy_environment_previous.clear()

    def on_proxy_toggled(self, enabled: bool) -> None:
        try:
            self._set_proxy_environment(enabled)
        except ValueError as exc:
            self.proxy_toggle_btn.blockSignals(True)
            self.proxy_toggle_btn.setChecked(False)
            self.proxy_toggle_btn.blockSignals(False)
            QMessageBox.warning(self, "Proxy Configuration Required", str(exc))
            enabled = False
        self.proxy_toggle_btn.setText("Proxy: On" if enabled else "Proxy: Off")
        self.proxy_toggle_btn.style().unpolish(self.proxy_toggle_btn)
        self.proxy_toggle_btn.style().polish(self.proxy_toggle_btn)
        self.proxy_toggle_btn.update()
        self.add_log(
            "Proxy environment variables enabled for new connections."
            if enabled
            else "Proxy environment variables disabled for new connections."
        )

    def check_connectivity(self) -> bool:
        url = self.archive_service_url_input.text().strip() or self.auth_server_input.text().strip()
        if not url:
            return False

        proxy_url = self.proxy_url_input.text().strip()
        proxies = {"http": proxy_url, "https": proxy_url} if self.proxy_toggle_btn.isChecked() and proxy_url else None

        try:
            session = requests.Session()
            session.trust_env = False
            response = session.get(url, timeout=(1, 2), proxies=proxies, verify=True)
            return response.status_code < 500
        except RequestException:
            return False

    def update_summary_cards(self) -> None:
        task_snapshots = self.snapshot_all_tasks()
        counts = calculate_status_counts(task_snapshots)
        total = counts["total"]
        successful = counts["completed"]
        in_progress = counts["in_progress"]
        failed = counts["failed"]
        pending = counts["pending"]
        canceled = counts["canceled"]

        completion_rate = 0 if total == 0 else int((successful / total) * 100)
        active_rate = 0 if total == 0 else int((in_progress / total) * 100)
        failure_rate = 0 if total == 0 else int((failed / total) * 100)

        total_subtitle = f"{pending} pending"
        if canceled:
            total_subtitle = f"{pending} pending | {canceled} canceled"

        self.summary_value_labels["total"].setText(str(total))
        self.summary_subtitle_labels["total"].setText(total_subtitle)
        self.summary_value_labels["successful"].setText(str(successful))
        self.summary_subtitle_labels["successful"].setText(f"{completion_rate}% completion rate")
        self.summary_value_labels["in_progress"].setText(str(in_progress))
        self.summary_subtitle_labels["in_progress"].setText(f"{active_rate}% active transfers")
        self.summary_value_labels["failed"].setText(str(failed))
        self.summary_subtitle_labels["failed"].setText(f"{failure_rate}% failure rate")

    def update_history_cards(self) -> None:
        """Retained as a compatibility hook after Analytics summary cards were removed."""
        # Analytics counts are now rendered in the side-navigation labels by
        # refresh_analytics_panel(), so there are no card widgets to update.
        return

    def recalculate_overall_progress(self) -> None:
        task_snapshots = self.snapshot_all_tasks()
        total_bytes = sum(int(snapshot["size_bytes"]) for snapshot in task_snapshots)
        progressed_bytes = 0.0

        for snapshot in task_snapshots:
            size_bytes = int(snapshot["size_bytes"])
            progress = int(snapshot["progress"])
            progressed_bytes += size_bytes * (progress / 100)

        percent = 0 if total_bytes <= 0 else int((progressed_bytes / total_bytes) * 100)
        self.overall_progress.setValue(percent)

    def _ensure_support_log_encryption_available(self) -> None:
        """Fail before archival when password-protected logging is unavailable."""
        try:
            from cryptography.fernet import Fernet  # noqa: F401
        except ImportError as exc:
            raise ValueError(
                "The cryptography package is required for mandatory encrypted support logs. "
                "Install it with: pip install cryptography"
            ) from exc

    def add_log(self, text: str) -> None:
        """Queue a password-encrypted log entry without blocking the UI thread."""
        log_file = self.current_log_file
        if log_file is None:
            return
        entry = f"[{current_timestamp()}] {text}"
        self._support_log_queue.put((log_file, entry))

    def _support_log_writer_loop(self) -> None:
        """Batch encryption work so GUI events never wait for PBKDF2 or disk I/O."""
        while True:
            first_item = self._support_log_queue.get()
            if first_item is None:
                self._support_log_queue.task_done()
                return
            pending: list[tuple[Path, str]] = [first_item]
            try:
                # Drain immediately available entries into one encryption cycle.
                while len(pending) < 50:
                    try:
                        next_item = self._support_log_queue.get_nowait()
                    except queue.Empty:
                        break
                    if next_item is None:
                        # Requeue the shutdown marker after this batch is durable.
                        self._support_log_queue.put(None)
                        self._support_log_queue.task_done()
                        break
                    pending.append(next_item)

                grouped_entries: dict[Path, list[str]] = {}
                for log_file, entry in pending:
                    grouped_entries.setdefault(log_file, []).append(entry)
                for log_file, entries in grouped_entries.items():
                    try:
                        self._append_encrypted_log_entries(log_file, entries)
                    except ArchiveError as exc:
                        # Do not create plaintext fallback files. The archive worker and
                        # GUI remain responsive; the failure is retained only in stderr.
                        print(f"Mandatory encrypted support logging failed: {exc}", flush=True)
            finally:
                for _ in pending:
                    self._support_log_queue.task_done()

    @staticmethod
    def _append_encrypted_log_entries(log_file: Path, entries: list[str]) -> None:
        """Append a batch to a Fernet log encrypted with Support Password: Admin@321."""
        if not entries:
            return
        try:
            from cryptography.fernet import Fernet, InvalidToken
        except ImportError as exc:
            raise ArchiveError("Protected support logging requires the 'cryptography' package.") from exc

        salt_file = log_file.with_suffix(".salt")
        try:
            log_file.parent.mkdir(parents=True, exist_ok=True)
            salt = salt_file.read_bytes() if salt_file.exists() else secrets.token_bytes(16)
            if len(salt) != 16:
                raise ArchiveError(f"Invalid salt length in {salt_file.name}; expected 16 bytes.")
            if not salt_file.exists():
                with salt_file.open("xb") as salt_handle:
                    salt_handle.write(salt)
                    salt_handle.flush()
                    os.fsync(salt_handle.fileno())
            key_material = pbkdf2_hmac(
                "sha256",
                SUPPORT_LOG_PASSWORD.encode("utf-8"),
                salt,
                390000,
                dklen=32,
            )
            cipher = Fernet(base64.urlsafe_b64encode(key_material))
            if log_file.exists():
                try:
                    previous_content = cipher.decrypt(log_file.read_bytes()).decode("utf-8")
                except InvalidToken as exc:
                    raise ArchiveError(
                        "Unable to decrypt the existing protected support log with the configured support credential."
                    ) from exc
            else:
                previous_content = ""
            encrypted_content = cipher.encrypt((previous_content + "\n".join(entries) + "\n").encode("utf-8"))
            with log_file.open("wb") as log_handle:
                log_handle.write(encrypted_content)
                log_handle.flush()
                os.fsync(log_handle.fileno())
        except OSError as exc:
            raise ArchiveError(f"Unable to write protected support log: {exc}") from exc

    def _is_current_user_authorized(self) -> bool:
        """Return whether the logged-in Windows user is allowed by config.json."""
        if not self.authorized_users:
            return False
        current_user = self.windows_user_name.casefold()
        return current_user in {user.casefold() for user in self.authorized_users}

    def ensure_worker_running(self) -> bool:
        if self.is_worker_running():
            return False
        if not self._is_current_user_authorized():
            QMessageBox.critical(
                self,
                "Archive Not Authorized",
                "The currently logged-in Windows user is not authorized to start archival. "
                "Ask an administrator to add this user to authorized_users in config.json.",
            )
            return False
        try:
            self._ensure_support_log_encryption_available()
            config = self.build_config()
        except ValueError as exc:
            QMessageBox.warning(self, "Missing Settings", str(exc))
            self.tabs.setCurrentWidget(self.settings_tab)
            return False
        if self.root_folder is None:
            QMessageBox.warning(self, "Folder Required", "Please select a folder first.")
            return False

        self._ensure_current_run_created()
        self.save_settings(show_message=False)
        self.refresh_btn.setEnabled(False)

        self.thread = QThread()
        self.worker = Worker(self.tasks, self.root_folder, config, self.task_lock, self.history_db, self.current_run_id)
        self.worker.moveToThread(self.thread)
        self.thread.started.connect(self.worker.run)
        self.worker.update_row.connect(self.on_task_progress_updated)
        self.worker.update_task_id.connect(self.update_task_id)
        self.worker.overall_progress.connect(self.overall_progress.setValue)
        self.worker.log.connect(self.add_log)
        self.worker.finished.connect(self.thread.quit)
        self.worker.finished.connect(self.worker.deleteLater)
        self.thread.finished.connect(self.on_processing_finished)
        self.thread.finished.connect(self.thread.deleteLater)
        self.thread.start()
        return True

    def is_worker_running(self) -> bool:
        return self.thread is not None and self.thread.isRunning()

    def on_processing_finished(self) -> None:
        self._set_archive_starting_state(False)
        self.refresh_btn.setEnabled(True)
        self.recalculate_overall_progress()
        self.update_summary_cards()
        self.persist_all_tasks()
        self.load_history_tables()
        self.refresh_analytics_panel()
        self._update_refresh_timestamp()
        self.add_log("Archive worker idle.")
        self.worker = None
        self.thread = None
        self.current_log_file = None
        self.schedule_post_run_refresh()

    def _prepare_worker_environment(self) -> bool:
        if self.root_folder is None or not self.tasks:
            QMessageBox.information(self, "Data Definition Required", "Prepare and move one or more files from the Data Definition page before starting archival.")
            self.tabs.setCurrentWidget(self.data_definition_tab)
            return False
        return True

    def _validated_source(self) -> Path | None:
        source_text = self.folder_input.text().strip()
        is_single_file = self.archive_source_mode.currentData() == "file"
        source_label = "file" if is_single_file else "folder"
        if not source_text:
            QMessageBox.warning(self, "Source Required", f"Please select a {source_label} first.")
            return None
        source_path = Path(source_text)
        if not source_path.exists() or (is_single_file and not source_path.is_file()) or (not is_single_file and not source_path.is_dir()):
            QMessageBox.warning(self, "Invalid Source", f"Please select a valid {source_label}.")
            return None
        return source_path

    def _validated_folder(self) -> Path | None:
        return self._validated_source()

    def _ensure_current_run_created(self) -> None:
        if self.current_run_id is not None or self.root_folder is None or not self.tasks:
            return
        snapshots = self.snapshot_all_tasks()
        self.current_run_id = self.history_db.create_run(str(self.root_folder), snapshots)
        logs_dir = logs_dir_path()
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.current_log_file = logs_dir / f"archive_run_{self.current_run_id}_{timestamp}.log.enc"
        self.persist_all_tasks()
        self.load_history_tables()
        self.add_log(f"Created archive run #{self.current_run_id}.")
        self.add_log(f"Run log file: {self.current_log_file}")
        self.add_log(
            "TECHNICAL | run_initialized | " + json.dumps(
                {
                    "run_id": self.current_run_id,
                    "root_folder": str(self.root_folder),
                    "task_count": len(self.tasks),
                    "application_storage": str(app_storage_dir()),
                    "history_database": str(self.history_db.db_path),
                    "encrypted_log": str(self.current_log_file),
                },
                ensure_ascii=False,
                separators=(",", ":"),
            )
        )

    def snapshot_task(self, row: int) -> dict[str, object] | None:
        with self.task_lock:
            task = next((candidate for candidate in self.tasks if candidate.row == row), None)
            if task is None:
                return None
            return {
                "row_index": task.row,
                "relative_path": task.relative_path,
                "full_path": task.full_path or str(task.file_path),
                "file_name": task.file_name or task.file_path.name,
                "file_hash": task.file_hash,
                "archived_at": task.archived_at,
                "commit_state": task.commit_state,
                "source_size": task.source_size,
                "source_mtime": task.source_mtime,
                "metadata_json": task.metadata_json,
                "size_bytes": task.size_bytes,
                "task_id": task.task_id,
                "progress": task.progress,
                "status": task.status,
                "updated_at": current_timestamp(),
            }

    def snapshot_all_tasks(self) -> list[dict[str, object]]:
        with self.task_lock:
            return [
                {
                    "row_index": task.row,
                    "relative_path": task.relative_path,
                    "full_path": task.full_path or str(task.file_path),
                    "file_name": task.file_name or task.file_path.name,
                    "file_hash": task.file_hash,
                    "archived_at": task.archived_at,
                    "commit_state": task.commit_state,
                    "source_size": task.source_size,
                    "source_mtime": task.source_mtime,
                    "metadata_json": task.metadata_json,
                    "size_bytes": task.size_bytes,
                    "task_id": task.task_id,
                    "progress": task.progress,
                    "status": task.status,
                    "updated_at": current_timestamp(),
                }
                for task in self.tasks
            ]

    def persist_task_state(self, row: int) -> None:
        if self.current_run_id is None:
            return
        snapshot = self.snapshot_task(row)
        if snapshot is None:
            return
        self.history_db.upsert_task(self.current_run_id, snapshot)
        self.history_db.update_run_summary(self.current_run_id, self.snapshot_all_tasks())

    def persist_all_tasks(self) -> None:
        if self.current_run_id is None:
            return
        snapshots = self.snapshot_all_tasks()
        for snapshot in snapshots:
            self.history_db.upsert_task(self.current_run_id, snapshot)
        self.history_db.update_run_summary(self.current_run_id, snapshots)

    def show_query_builder(self) -> None:
        self.query_builder_frame.setVisible(True)
        self.build_query_btn.setVisible(False)
        self.close_query_btn.setVisible(True)

    def hide_query_builder(self) -> None:
        self.query_builder_frame.setVisible(False)
        self.close_query_btn.setVisible(False)
        self.build_query_btn.setVisible(True)
        self.update_active_query_note()

    def run_history_query(self) -> None:
        self.query_applied = True
        self.load_history_tables()

    def add_query_clause(self) -> None:
        row = self.query_table.rowCount()
        self.query_table.insertRow(row)

        if row == 0:
            self.query_table.setCellWidget(row, 0, QLabel(""))
        else:
            and_or_combo = QComboBox()
            and_or_combo.addItems(["AND", "OR"])
            self.query_table.setCellWidget(row, 0, and_or_combo)

        field_combo = QComboBox()
        field_combo.addItems(QUERY_FIELD_OPTIONS)
        field_combo.currentTextChanged.connect(lambda _value, r=row: self._update_query_value_widget(r))
        self.query_table.setCellWidget(row, 1, field_combo)

        operator_combo = QComboBox()
        operator_combo.addItems(["contains", "equals", "starts with", "ends with"])
        self.query_table.setCellWidget(row, 2, operator_combo)

        self._set_query_value_widget(row, field_combo.currentText())

        if row == 0:
            self.query_table.setCellWidget(row, 4, QLabel(""))
        else:
            remove_btn = QPushButton("×")
            remove_btn.setObjectName("removeClauseButton")
            remove_btn.setToolTip("Remove clause")
            remove_btn.clicked.connect(lambda _checked=False, r=row: self.remove_query_clause(r))
            self.query_table.setCellWidget(row, 4, remove_btn)
        self._refresh_query_clause_controls()

    def remove_query_clause(self, row: int) -> None:
        if self.query_table.rowCount() <= 1:
            field_widget = self.query_table.cellWidget(0, 1)
            operator_widget = self.query_table.cellWidget(0, 2)
            if isinstance(field_widget, QComboBox):
                field_widget.setCurrentIndex(0)
            if isinstance(operator_widget, QComboBox):
                operator_widget.setCurrentIndex(0)
            self._set_query_value_widget(0, field_widget.currentText() if isinstance(field_widget, QComboBox) else "")
            value_widget = self.query_table.cellWidget(0, 3)
            if isinstance(value_widget, QLineEdit):
                value_widget.clear()
            elif isinstance(value_widget, QDateTimeEdit):
                value_widget.setDate(QDate.currentDate())
            return
        self.query_table.removeRow(row)
        self._refresh_query_clause_controls()

    def _set_query_value_widget(self, row: int, field_name: str) -> None:
        existing_widget = self.query_table.cellWidget(row, 3)
        if field_name == "Archival Timestamp":
            if isinstance(existing_widget, QDateTimeEdit):
                return
            date_widget = QDateTimeEdit()
            date_widget.setCalendarPopup(True)
            date_widget.setDisplayFormat("yyyy-MM-dd")
            date_widget.setDate(QDate.currentDate())
            date_widget.setTime(QTime(0, 0, 0))
            date_widget.setButtonSymbols(QDateTimeEdit.UpDownArrows)
            date_widget.calendarWidget().setGridVisible(True)
            self.query_table.setCellWidget(row, 3, date_widget)
        else:
            if isinstance(existing_widget, QLineEdit):
                if field_name == "Archive Metadata":
                    existing_widget.setPlaceholderText("e.g. project-code or ABC123")
                else:
                    existing_widget.setPlaceholderText("Enter value")
                return
            value_input = QLineEdit()
            value_input.setPlaceholderText(
                "e.g. project-code or ABC123" if field_name == "Archive Metadata" else "Enter value"
            )
            self.query_table.setCellWidget(row, 3, value_input)

    def _update_query_value_widget(self, row: int) -> None:
        field_widget = self.query_table.cellWidget(row, 1)
        if isinstance(field_widget, QComboBox):
            self._set_query_value_widget(row, field_widget.currentText())

    def _refresh_query_clause_controls(self) -> None:
        for row in range(self.query_table.rowCount()):
            and_or_widget = self.query_table.cellWidget(row, 0)
            if row == 0:
                if not isinstance(and_or_widget, QLabel):
                    self.query_table.setCellWidget(row, 0, QLabel(""))
            elif isinstance(and_or_widget, QComboBox):
                and_or_widget.setEnabled(True)

            remove_widget = self.query_table.cellWidget(row, 4)
            if row == 0:
                if not isinstance(remove_widget, QLabel):
                    self.query_table.setCellWidget(row, 4, QLabel(""))
            elif isinstance(remove_widget, QPushButton):
                try:
                    remove_widget.clicked.disconnect()
                except Exception:
                    pass
                remove_widget.clicked.connect(lambda _checked=False, r=row: self.remove_query_clause(r))

    def toggle_filter_columns_menu(self) -> None:
        """Show or explicitly dismiss the persistent Filter Columns popup."""
        if self.filter_columns_popup.isVisible():
            self.filter_columns_popup.hide()
            return
        position = self.filter_columns_btn.mapToGlobal(self.filter_columns_btn.rect().bottomLeft())
        self.filter_columns_popup.move(position)
        self.filter_columns_popup.show()
        self.filter_columns_popup.raise_()

    def _initialize_filter_column_menu(self) -> None:
        """Build persistent column controls without QMenu check indicators."""
        popup_layout = QVBoxLayout(self.filter_columns_popup)
        popup_layout.setContentsMargins(8, 8, 8, 8)
        popup_layout.setSpacing(2)
        column_names = ["Run ID", "File Name", "Full Path", "Size", "File Hash", "Task ID", "Status", "Archival Timestamp"]
        asset_dir = Path(__file__).resolve().parent
        for index, name in enumerate(column_names, start=1):
            row = QFrame(self.filter_columns_popup)
            row.setObjectName("filterColumnsRow")
            row_layout = QHBoxLayout(row)
            row_layout.setContentsMargins(8, 5, 10, 5)
            row_layout.setSpacing(8)

            control = SvgToggleButton(
                asset_dir / "checked.svg",
                asset_dir / "unchecked.svg",
                row,
                accessible_name=f"Show {name} column",
                tooltip=f"Show {name} column",
            )
            # Initialization is intentionally signal-free: visibility changes only
            # in response to a user toggle, not a programmatic state reflection.
            with QSignalBlocker(control):
                control.setChecked(True)
            control.toggled.connect(partial(self.set_history_column_visible, index))
            self.column_controls[index] = control

            label = FilterColumnRowLabel(name, row)
            label.setObjectName("filterColumnsRowLabel")
            label.setMinimumHeight(18)
            label.setCursor(Qt.PointingHandCursor)
            label.clicked.connect(control.click)
            row_layout.addWidget(control)
            row_layout.addWidget(label, 1)
            popup_layout.addWidget(row)
        popup_layout.addStretch()

    def set_history_column_visible(self, column: int, visible: bool) -> None:
        self.history_table.setColumnHidden(column, not visible)
        self._apply_history_table_column_widths()

    def _apply_history_table_column_widths(self) -> None:
        header = self.history_table.horizontalHeader()
        header.setSectionResizeMode(self.history_checkbox_column, QHeaderView.Fixed)
        self.history_table.setColumnWidth(self.history_checkbox_column, 46)
        for column in range(1, self.history_table.columnCount()):
            if not self.history_table.isColumnHidden(column):
                header.setSectionResizeMode(column, QHeaderView.Stretch)
        if isinstance(header, CheckboxHeaderView):
            header._position_checkbox()

    def _history_row_key(self, row: int) -> tuple[str, ...] | None:
        values: list[str] = []
        for column in range(1, self.history_table.columnCount()):
            item = self.history_table.item(row, column)
            if item is None:
                return None
            values.append(item.text())
        return tuple(values)

    def _history_checkbox_at(self, row: int) -> SvgToggleButton | None:
        container = self.history_table.cellWidget(row, self.history_checkbox_column)
        if container is None:
            return None
        return container.findChild(SvgToggleButton, "historyRowToggle")

    def _capture_history_checked_keys(self) -> None:
        checked_keys: set[tuple[str, ...]] = set()
        for row in range(self.history_table.rowCount()):
            checkbox = self._history_checkbox_at(row)
            if checkbox is not None and checkbox.isChecked():
                row_key = self._history_row_key(row)
                if row_key is not None:
                    checked_keys.add(row_key)
        self.history_checked_keys = checked_keys

    def on_history_row_checkbox_changed(self, _checked: bool) -> None:
        if self.loading_history_table:
            return
        self._capture_history_checked_keys()
        self._sync_history_header_checkbox()

    def on_history_header_checkbox_clicked(self, checked: bool) -> None:
        """Apply the header's boolean click state to every currently visible row."""
        if not self.loading_history_table:
            self._set_all_history_checkboxes(checked)

    def _set_all_history_checkboxes(self, checked: bool) -> None:
        previous_loading_state = self.loading_history_table
        self.loading_history_table = True
        blockers: list[QSignalBlocker] = []
        try:
            for row in range(self.history_table.rowCount()):
                checkbox = self._history_checkbox_at(row)
                if checkbox is not None:
                    blockers.append(QSignalBlocker(checkbox))
                    checkbox.setChecked(checked)
        finally:
            self.loading_history_table = previous_loading_state
        self._capture_history_checked_keys()
        self._sync_history_header_checkbox()

    def _sync_history_header_checkbox(self) -> None:
        all_checked = self.history_table.rowCount() > 0 and all(
            (checkbox := self._history_checkbox_at(row)) is not None and checkbox.isChecked()
            for row in range(self.history_table.rowCount())
        )
        # This is a programmatic reflection of the row state, never a bulk-toggle request.
        blocker = QSignalBlocker(self.history_select_all_checkbox)
        try:
            self.history_select_all_checkbox.setChecked(all_checked)
        finally:
            del blocker

    def _current_query_summary(self) -> str:
        clauses: list[str] = []
        for row in range(self.query_table.rowCount()):
            and_or_widget = self.query_table.cellWidget(row, 0)
            field_widget = self.query_table.cellWidget(row, 1)
            operator_widget = self.query_table.cellWidget(row, 2)
            value_widget = self.query_table.cellWidget(row, 3)
            if not isinstance(field_widget, QComboBox) or not isinstance(operator_widget, QComboBox):
                continue
            if isinstance(value_widget, QLineEdit):
                value_text = value_widget.text().strip()
            elif isinstance(value_widget, QDateTimeEdit):
                value_text = value_widget.dateTime().toString("yyyy-MM-dd").strip()
            else:
                continue
            if not value_text:
                continue
            prefix = ""
            if clauses and isinstance(and_or_widget, QComboBox):
                prefix = f" {and_or_widget.currentText()} "
            clauses.append(f"{prefix}{field_widget.currentText()} {operator_widget.currentText()} '{value_text}'")
        return "".join(clauses)

    def update_active_query_note(self) -> None:
        query_summary = self._current_query_summary().strip()
        if self.query_applied and query_summary:
            self.active_query_note.setText(f"Query currently applied on data: {query_summary}")
            self.active_query_note.setVisible(True)
        else:
            self.active_query_note.clear()
            self.active_query_note.setVisible(False)

    def export_history_table(self) -> None:
        self._capture_history_checked_keys()
        selected_rows = self.selected_history_rows()
        if not selected_rows:
            QMessageBox.information(self, "No Rows Selected", "Select one or more history rows using the checkboxes before exporting.")
            return

        file_path, _ = QFileDialog.getSaveFileName(self, "Export History", "archive_history.csv", "CSV Files (*.csv);;All Files (*)")
        if not file_path:
            return

        visible_columns = [column for column in range(1, self.history_table.columnCount()) if not self.history_table.isColumnHidden(column)]
        try:
            import csv
            with open(file_path, "w", newline="", encoding="utf-8") as handle:
                writer = csv.writer(handle)
                writer.writerow([self.history_table.horizontalHeaderItem(column).text() for column in visible_columns])
                for row in selected_rows:
                    writer.writerow([self.history_table.item(row, column).text() if self.history_table.item(row, column) is not None else "" for column in visible_columns])
        except Exception as exc:  # noqa: BLE001
            QMessageBox.critical(self, "Export Failed", f"Unable to export history.\n{exc}")
            return

        QMessageBox.information(self, "Export Complete", f"History exported to:\n{file_path}")

    def selected_history_rows(self) -> list[int]:
        selected_rows: list[int] = []
        for row in range(self.history_table.rowCount()):
            checkbox = self._history_checkbox_at(row)
            if checkbox is not None and checkbox.isChecked():
                selected_rows.append(row)
        return selected_rows

    def clear_history_filters(self) -> None:
        self.history_checked_keys.clear()
        self.keyword_input.clear()
        self.query_applied = False
        self.hide_query_builder()

        while self.query_table.rowCount() > 1:
            self.query_table.removeRow(self.query_table.rowCount() - 1)
        self._refresh_query_clause_controls()

        for row in range(self.query_table.rowCount()):
            field_widget = self.query_table.cellWidget(row, 1)
            operator_widget = self.query_table.cellWidget(row, 2)
            value_widget = self.query_table.cellWidget(row, 3)
            if isinstance(field_widget, QComboBox):
                field_widget.setCurrentIndex(0)
                self._set_query_value_widget(row, field_widget.currentText())
                value_widget = self.query_table.cellWidget(row, 3)
            if isinstance(operator_widget, QComboBox):
                operator_widget.setCurrentIndex(0)
            if isinstance(value_widget, QLineEdit):
                value_widget.clear()
            elif isinstance(value_widget, QDateTimeEdit):
                value_widget.setDate(QDate.currentDate())
        self.update_active_query_note()
        self.load_history_tables()
        self._set_all_history_checkboxes(False)

    @staticmethod
    def _metadata_json_strings(value: object) -> tuple[str, str]:
        """Return compact display JSON and pretty tooltip JSON for persisted metadata.

        Existing database rows predate this field, and malformed legacy values are
        retained verbatim rather than making History unavailable.
        """
        raw = str(value or "").strip()
        if not raw:
            return "{}", "{}"
        try:
            payload = json.loads(raw)
        except (TypeError, ValueError):
            return raw, raw
        return (
            json.dumps(payload, ensure_ascii=False, separators=(",", ":")),
            json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True),
        )

    def _metadata_display_json(self, value: object) -> str:
        return self._metadata_json_strings(value)[0]

    def _matches_query_clause(self, item: sqlite3.Row, field_name: str, operator_name: str, target_value: str) -> bool:
        field_map = {
            "Run ID": str(item["run_id"]),
            "File Name": str(item["file_name"] or Path(str(item["full_path"])).name),
            "Full Path": str(item["full_path"] or item["relative_path"]),
            "Size": format_size(int(item["size_bytes"])),
            "File Hash": str(item["file_hash"]),
            "Task ID": str(item["task_id"]),
            "Status": str(item["status"]),
            "Archival Timestamp": str(item["archived_at"]),
            "Archive Metadata": self._metadata_display_json(item["metadata_json"]),
        }
        source_value = field_map.get(field_name, "")
        source_compare = source_value.casefold()
        target_compare = target_value.casefold()

        if operator_name == "equals":
            return source_compare == target_compare
        if operator_name == "starts with":
            return source_compare.startswith(target_compare)
        if operator_name == "ends with":
            return source_compare.endswith(target_compare)
        return target_compare in source_compare

    def _matches_query_builder(self, item: sqlite3.Row) -> bool:
        clauses: list[tuple[str, str, str, str]] = []
        for row in range(self.query_table.rowCount()):
            and_or_widget = self.query_table.cellWidget(row, 0)
            field_widget = self.query_table.cellWidget(row, 1)
            operator_widget = self.query_table.cellWidget(row, 2)
            value_widget = self.query_table.cellWidget(row, 3)
            if not isinstance(field_widget, QComboBox) or not isinstance(operator_widget, QComboBox):
                continue
            if isinstance(value_widget, QLineEdit):
                value_text = value_widget.text().strip()
            elif isinstance(value_widget, QDateTimeEdit):
                value_text = value_widget.dateTime().toString("yyyy-MM-dd").strip()
            else:
                continue
            if not value_text:
                continue
            and_or_value = and_or_widget.currentText() if isinstance(and_or_widget, QComboBox) and row > 0 else "AND"
            clauses.append((and_or_value, field_widget.currentText(), operator_widget.currentText(), value_text))

        if not clauses:
            return True

        grouped_values: dict[tuple[str, str], dict[str, list[str]]] = {}
        ordered_groups: list[tuple[str, str]] = []
        for _and_or_value, field_name, operator_name, value_text in clauses:
            group_key = (field_name, operator_name)
            if group_key not in grouped_values:
                grouped_values[group_key] = {"contains": []}
                ordered_groups.append(group_key)
            grouped_values[group_key]["contains"].append(value_text)

        group_results: list[tuple[str, bool]] = []
        first_clause_and_or = "AND"
        for index, (and_or_value, field_name, operator_name, value_text) in enumerate(clauses):
            group_key = (field_name, operator_name)
            if group_key not in grouped_values:
                continue
            values = grouped_values.pop(group_key)["contains"]
            if operator_name == "contains" and len(values) > 1:
                clause_result = any(self._matches_query_clause(item, field_name, operator_name, value) for value in values)
            else:
                clause_result = self._matches_query_clause(item, field_name, operator_name, value_text)
            connector = and_or_value if index > 0 else "AND"
            group_results.append((connector, clause_result))

        if not group_results:
            return True

        result = group_results[0][1]
        for connector, clause_result in group_results[1:]:
            if connector == "OR":
                result = result or clause_result
            else:
                result = result and clause_result
        return result

    def _filtered_history(self, task_history: list[sqlite3.Row]) -> list[sqlite3.Row]:
        keyword = self.keyword_input.text().strip().casefold()

        filtered = task_history
        if keyword:
            filtered = [
                item
                for item in filtered
                if keyword in str(item["run_id"]).casefold()
                or keyword in str(item["file_name"] or Path(str(item["full_path"])).name).casefold()
                or keyword in str(item["full_path"] or item["relative_path"]).casefold()
                or keyword in str(item["task_id"]).casefold()
                or keyword in str(item["status"]).casefold()
                or keyword in str(item["file_hash"]).casefold()
                or keyword in str(item["archived_at"]).split(" ")[0].casefold()
                or keyword in self._metadata_display_json(item["metadata_json"]).casefold()
            ]
        if self.query_applied:
            filtered = [item for item in filtered if self._matches_query_builder(item)]
        return filtered

    def load_history_tables(self) -> None:
        self._capture_history_checked_keys()
        self.update_history_cards()
        task_history = self.history_db.fetch_task_history(limit=500)
        completed_history = [item for item in task_history if str(item["status"]) == "Completed"]
        filtered_history = self._filtered_history(completed_history)
        self.loading_history_table = True
        self.history_table.setRowCount(0)
        for row_index, item in enumerate(filtered_history):
            self.history_table.insertRow(row_index)
            row_values = (
                str(item["run_id"]),
                str(item["file_name"] or Path(str(item["full_path"])).name),
                str(item["full_path"] or item["relative_path"]),
                format_size(int(item["size_bytes"])),
                str(item["file_hash"]),
                str(item["task_id"]),
                str(item["status"]),
                str(item["archived_at"]).split(" ")[0],
            )
            checkbox_container = QWidget()
            checkbox_container.setObjectName("historyRowCheckboxContainer")
            checkbox_layout = QHBoxLayout(checkbox_container)
            checkbox_layout.setContentsMargins(0, 0, 0, 0)
            checkbox_layout.setAlignment(Qt.AlignCenter)
            asset_dir = Path(__file__).resolve().parent
            checkbox = SvgToggleButton(
                asset_dir / "checked.svg",
                asset_dir / "unchecked.svg",
                checkbox_container,
                accessible_name="Select history row",
                tooltip="Select history row",
            )
            checkbox.setObjectName("historyRowToggle")
            checkbox.setChecked(row_values in self.history_checked_keys)
            checkbox_layout.addWidget(checkbox)
            self.history_table.setCellWidget(row_index, self.history_checkbox_column, checkbox_container)
            for column, value in enumerate(row_values, start=1):
                table_item = QTableWidgetItem(value)
                table_item.setTextAlignment(Qt.AlignCenter)
                self.history_table.setItem(row_index, column, table_item)
            checkbox.toggled.connect(self.on_history_row_checkbox_changed)

        self.loading_history_table = False
        self._sync_history_header_checkbox()
        self.update_active_query_note()
        self._apply_history_table_column_widths()
        self.history_table.resizeRowsToContents()

    def _update_refresh_timestamp(self) -> None:
        self.last_refresh_label.setText(f"Last refreshed: {current_timestamp()}")

    def schedule_post_run_refresh(self) -> None:
        self.post_run_refresh_timer.stop()
        self.post_run_warning_timer.stop()
        self.countdown_timer.stop()
        self.hide_refresh_notice_banner()
        self.post_run_warning_timer.start(20000)
        self.post_run_refresh_timer.start(30000)

    def show_post_run_countdown(self) -> None:
        self.countdown_remaining = 10
        self.refresh_notice_banner.setVisible(True)
        self.update_refresh_notice_banner()
        self.countdown_timer.start()

    def update_refresh_notice_banner(self) -> None:
        if self.countdown_remaining <= 0:
            self.countdown_timer.stop()
            self.hide_refresh_notice_banner()
            return
        self.refresh_notice_banner.setText(
            f"Auto-refresh in {self.countdown_remaining}s — completed and canceled files will be "
            "removed; stopped, queued, and waiting-network files remain."
        )
        self.countdown_remaining -= 1

    def hide_refresh_notice_banner(self) -> None:
        self.refresh_notice_banner.setVisible(False)
        self.refresh_notice_banner.clear()
        self.countdown_remaining = 0

    def finalize_post_run_refresh(self) -> None:
        self.countdown_timer.stop()
        self.hide_refresh_notice_banner()
        self.keep_only_stopped_tasks()
        if not self.tasks:
            self.folder_input.clear()
            self.root_folder = None
            self.current_run_id = None
            self.add_log("No transfer tasks remain; cleared the selected archive source.")
        self.update_summary_cards()
        self.recalculate_overall_progress()
        self._update_refresh_timestamp()
        self.add_log(
            "Home page auto-refreshed after run completion; stopped, queued, and waiting-network files remain."
        )

    def keep_only_stopped_tasks(self) -> None:
        preserved_statuses = {"Stopped", "Queued", "Ready", WAITING_FOR_NETWORK_STATUS}
        preserved_tasks = [task for task in self.tasks if task.status in preserved_statuses]
        self.table.setRowCount(0)
        self.tasks = []

        for display_row, task in enumerate(preserved_tasks):
            # Preserve the original task.row so resumed tasks remain under the
            # same archive run_id and archive_tasks row_index in SQLite.
            self.tasks.append(task)
            self._insert_task_row_at(display_row, task)

    def resizeEvent(self, event) -> None:  # noqa: N802
        super().resizeEvent(event)
        if hasattr(self, "config_required_overlay") and hasattr(self, "data_definition_tab"):
            self.config_required_overlay.setGeometry(self.data_definition_tab.rect())

    def closeEvent(self, event) -> None:  # noqa: N802
        # Finish queued encrypted entries before the application exits.
        self._support_log_queue.join()
        self._support_log_queue.put(None)
        self._support_log_writer_thread.join(timeout=5)
        if self.history_db is not None:
            self.history_db.close()
        super().closeEvent(event)

    def apply_styles(self) -> None:
        self.setStyleSheet(
            """
            QMainWindow {
                background: #f5f5f7;
            }

            QLabel#archiveStartingBanner {
                background: #fff8dd;
                color: #7a5300;
                border: 1px solid #e6c665;
                border-radius: 8px;
                padding: 9px 12px;
                font-size: 10pt;
                font-weight: 600;
            }

            QFrame#configRequiredOverlay {
                background: rgba(245, 245, 247, 248);
                border: 1px solid #d8dbe3;
                border-radius: 10px;
            }

            QLabel#configRequiredOverlayTitle {
                color: #0b1437;
                font-size: 18pt;
                font-weight: 700;
            }

            QLabel#configRequiredOverlayMessage {
                color: #596174;
                font-size: 11pt;
                max-width: 500px;
            }

            QLabel#dashboardTitle {
                font-size: 22px;
                font-weight: 700;
                color: #0b1437;
            }

            QLabel#refreshLabel {
                color: #7a8191;
                font-size: 10pt;
            }

            QLabel#refreshNoticeBanner {
                background: #f1efff;
                color: #44357d;
                border: 1px solid #cfc8f7;
                border-radius: 7px;
                padding: 5px 9px;
                font-size: 9pt;
                font-weight: 600;
            }

            QLabel#sectionLabel {
                color: #0b1437;
                font-size: 11pt;
                font-weight: 600;
                margin-top: 4px;
            }

            QLabel#analyticsRowCount {
                color: #64748b;
                background: #f1f5f9;
                border: 1px solid #d8e0ea;
                border-radius: 8px;
                padding: 2px 7px;
                font-size: 8.5pt;
                font-weight: 600;
            }

            QLabel#liveBadge {
                background: #e8fbf2;
                color: #12a56b;
                border: 1px solid #bde9d2;
                border-radius: 11px;
                padding: 2px 9px;
                font-size: 9pt;
                font-weight: 600;
            }

            QLabel#offlineBadge {
                background: #fdecec;
                color: #d64545;
                border: 1px solid #f2b5b5;
                border-radius: 11px;
                padding: 2px 9px;
                font-size: 9pt;
                font-weight: 600;
            }

            QLabel#summaryTitle {
                color: #7a8191;
                font-size: 9pt;
                font-weight: 700;
                letter-spacing: 0.4px;
            }

            QLabel#summaryValue {
                color: #0b1437;
                font-size: 18pt;
                font-weight: 700;
            }

            QLabel#summarySubtitle {
                color: #7a8191;
                font-size: 9pt;
                font-weight: 600;
            }

            QLabel#queryNoteLabel {
                color: #0b1437;
                background: #eef4ff;
                border: 1px solid #c9dafc;
                border-radius: 8px;
                padding: 8px 12px;
                font-size: 10pt;
                font-weight: 600;
            }

            QPushButton#replicateMetadataButton {
                background: #eef4ff;
                color: #2f72d6;
                border: 1px solid #c9dafc;
                border-radius: 5px;
                padding: 3px 6px;
                min-width: 96px;
                font-size: 8pt;
                font-weight: 600;
            }

            QPushButton#replicateMetadataButton:hover {
                background: #dfeaff;
                color: #1d5fb8;
            }

            QPushButton#proxyToggleButton {
                background: #ffffff;
                color: #64748b;
                border: 1px solid #cbd5e1;
                min-width: 96px;
            }

            QPushButton#proxyToggleButton:hover {
                background: #f8fafc;
                color: #334155;
            }

            QPushButton#proxyToggleButton:checked {
                background: #eef4ff;
                color: #2f72d6;
                border: 1px solid #2f72d6;
            }

            QPushButton#secondaryActionButton, QToolButton#secondaryActionButton {
                background: white;
                color: #0b1437;
                border: 1px solid #2f72d6;
                min-width: 110px;
            }

            QPushButton#secondaryActionButton:hover, QToolButton#secondaryActionButton:hover {
                background: #f3f6fb;
                color: #0b1437;
            }

            QPushButton#filterColumnsButton {
                background: white;
                color: #0b1437;
                border: 1px solid #7b61ff;
                border-radius: 8px;
                padding: 8px 12px;
                min-width: 132px;
                font-weight: 600;
            }

            QPushButton#filterColumnsButton:hover,
            QPushButton#filterColumnsButton:pressed {
                background: #f5f0ff;
                color: #6b4ee6;
                border-color: #7b61ff;
            }

            QMenu {
                background: white;
                color: #0b1437;
                border: 1px solid #d8dbe3;
                border-radius: 8px;
                padding: 6px;
            }

            QMenu::item {
                padding: 7px 26px 7px 10px;
                border-radius: 5px;
            }

            QMenu::item:selected {
                background: #f5f0ff;
                color: #0b1437;
            }

            QFrame#filterColumnsPopup {
                background: white;
                color: #0b1437;
                border: 1px solid #d8dbe3;
                border-radius: 8px;
            }

            QFrame#filterColumnsRow {
                border: none;
                border-radius: 5px;
            }

            QFrame#filterColumnsRow:hover {
                background: #f5f0ff;
            }

            QLabel#filterColumnsRowLabel {
                color: #0b1437;
                border: none;
                background: transparent;
            }

            QPushButton#dangerActionButton {
                background: #d64545;
                color: white;
                border: 1px solid #b83232;
                border-radius: 8px;
                padding: 8px 12px;
                font-weight: 600;
                min-width: 96px;
            }

            QPushButton#dangerActionButton:hover {
                background: #b83232;
                border-color: #922929;
            }

            QPushButton#dangerActionButton:pressed {
                background: #922929;
                border-color: #762121;
            }

            QPushButton#dangerActionButton:disabled {
                background: #e9a5a5;
                color: #fff5f5;
                border-color: #e9a5a5;
            }

            QPushButton#closeQueryButton {
                background: white;
                color: #e1525c;
                border: 1px solid #e1525c;
                min-width: 110px;
                padding-left: 18px;
                padding-right: 18px;
            }

            QPushButton#closeQueryButton:hover {
                background: #fff1f2;
                color: #e1525c;
            }

            QPushButton#blueOutlineButton {
                background: white;
                color: #2f72d6;
                border: 1px solid #2f72d6;
                min-width: 150px;
            }

            QPushButton#blueOutlineButton:hover {
                background: #f3f6fb;
                color: #2f72d6;
            }

            QPushButton#warningOutlineButton {
                background: white;
                color: #d49a00;
                border: 1px solid #d49a00;
                min-width: 140px;
            }

            QPushButton#warningOutlineButton:hover {
                background: #fff9e6;
                color: #d49a00;
            }

            QPushButton#violetOutlineButton {
                background: white;
                color: #7b61ff;
                border: 1px solid #7b61ff;
                min-width: 120px;
            }

            QPushButton#violetOutlineButton:hover {
                background: #f5f0ff;
                color: #7b61ff;
            }

            QPushButton#successOutlineButton {
                background: white;
                color: #1f8f45;
                border: 1px solid #1f8f45;
                min-width: 140px;
            }

            QPushButton#successOutlineButton:hover {
                background: #edf9f0;
                color: #1f8f45;
            }

            QPushButton#removeClauseButton {
                background: white;
                color: #e1525c;
                border: 1px solid #e1525c;
                min-width: 28px;
                max-width: 28px;
                min-height: 28px;
                max-height: 28px;
                padding: 0px;
                font-size: 13pt;
                font-weight: 700;
            }

            QPushButton#removeClauseButton:hover {
                background: #fff1f2;
                color: #e1525c;
            }

            QFrame#queryBuilderFrame {
                background: #f7f7f9;
                border: 1px solid #d8dbe3;
                border-radius: 8px;
            }

            QTableWidget {
                background: white;
                font-size: 10pt;
                gridline-color: #d9d9d9;
                alternate-background-color: #fafafa;
                border: 1px solid #d8dbe3;
                border-radius: 8px;
            }

            QTableWidget::item {
                text-align: center;
            }

            QTableWidget::indicator {
                width: 12px;
                height: 12px;
                border-radius: 3px;
                border: 1px solid #2f72d6;
                background: white;
            }

            QTableWidget::indicator:unchecked {
                background: white;
                border: 1px solid #b8c2d9;
            }

            QTableWidget::indicator:checked {
                background: #2f72d6;
                border: 1px solid #2f72d6;
                image: none;
            }

            QHeaderView::section {
                background: #eef1f6;
                padding: 7px;
                border: 1px solid #d9dee8;
                font-weight: 600;
            }

            QHeaderView::section:first {
                border-top-left-radius: 8px;
            }

            QHeaderView::section:last {
                border-top-right-radius: 8px;
            }

            QHeaderView::section:hover {
                background: #e3edff;
                color: #1d5fb8;
            }

            QPushButton {
                background: #0b1437;
                color: white;
                border-radius: 8px;
                padding: 8px 12px;
                font-weight: 600;
                min-width: 96px;
            }

            QPushButton:hover {
                background: #16204a;
            }

            QPushButton:disabled {
                background: #9eb8d6;
                color: #f0f0f0;
            }

            QPushButton#replicateMetadataButton {
                background: #eef4ff;
                color: #2f72d6;
                border: 1px solid #c9dafc;
                border-radius: 5px;
                padding: 3px 6px;
                min-width: 96px;
                font-size: 8pt;
                font-weight: 600;
            }

            QPushButton#replicateMetadataButton:hover {
                background: #dfeaff;
                color: #1d5fb8;
            }

            QPushButton#proxyToggleButton {
                background: #ffffff;
                color: #64748b;
                border: 1px solid #cbd5e1;
                min-width: 96px;
            }

            QPushButton#proxyToggleButton:hover {
                background: #f8fafc;
                color: #334155;
            }

            QPushButton#proxyToggleButton:checked {
                background: #eef4ff;
                color: #2f72d6;
                border: 1px solid #2f72d6;
            }

            QPushButton#secondaryActionButton, QToolButton#secondaryActionButton {
                background: white;
                color: #0b1437;
                border: 1px solid #2f72d6;
                min-width: 110px;
            }

            QPushButton#secondaryActionButton:hover, QToolButton#secondaryActionButton:hover {
                background: #f3f6fb;
                color: #0b1437;
            }

            QPushButton#filterColumnsButton {
                background: white;
                color: #0b1437;
                border: 1px solid #7b61ff;
                border-radius: 8px;
                padding: 8px 12px;
                min-width: 132px;
                font-weight: 600;
            }

            QPushButton#filterColumnsButton:hover,
            QPushButton#filterColumnsButton:pressed {
                background: #f5f0ff;
                color: #6b4ee6;
                border-color: #7b61ff;
            }

            QMenu {
                background: white;
                color: #0b1437;
                border: 1px solid #d8dbe3;
                border-radius: 8px;
                padding: 6px;
            }

            QMenu::item {
                padding: 7px 26px 7px 10px;
                border-radius: 5px;
            }

            QMenu::item:selected {
                background: #f5f0ff;
                color: #0b1437;
            }

            QFrame#filterColumnsPopup {
                background: white;
                color: #0b1437;
                border: 1px solid #d8dbe3;
                border-radius: 8px;
            }

            QFrame#filterColumnsRow {
                border: none;
                border-radius: 5px;
            }

            QFrame#filterColumnsRow:hover {
                background: #f5f0ff;
            }

            QLabel#filterColumnsRowLabel {
                color: #0b1437;
                border: none;
                background: transparent;
            }

            QPushButton#dangerActionButton {
                background: #d64545;
                color: white;
                border: 1px solid #b83232;
                border-radius: 8px;
                padding: 8px 12px;
                font-weight: 600;
                min-width: 96px;
            }

            QPushButton#dangerActionButton:hover {
                background: #b83232;
                border-color: #922929;
            }

            QPushButton#dangerActionButton:pressed {
                background: #922929;
                border-color: #762121;
            }

            QPushButton#dangerActionButton:disabled {
                background: #e9a5a5;
                color: #fff5f5;
                border-color: #e9a5a5;
            }

            QPushButton#closeQueryButton {
                background: white;
                color: #e1525c;
                border: 1px solid #e1525c;
                min-width: 110px;
                padding-left: 18px;
                padding-right: 18px;
            }

            QPushButton#closeQueryButton:hover {
                background: #fff1f2;
                color: #e1525c;
            }

            QPushButton#blueOutlineButton {
                background: white;
                color: #2f72d6;
                border: 1px solid #2f72d6;
                min-width: 150px;
            }

            QPushButton#blueOutlineButton:hover {
                background: #f3f6fb;
                color: #2f72d6;
            }

            QPushButton#warningOutlineButton {
                background: white;
                color: #d49a00;
                border: 1px solid #d49a00;
                min-width: 140px;
            }

            QPushButton#warningOutlineButton:hover {
                background: #fff9e6;
                color: #d49a00;
            }

            QPushButton#violetOutlineButton {
                background: white;
                color: #7b61ff;
                border: 1px solid #7b61ff;
                min-width: 120px;
            }

            QPushButton#violetOutlineButton:hover {
                background: #f5f0ff;
                color: #7b61ff;
            }

            QPushButton#successOutlineButton {
                background: white;
                color: #1f8f45;
                border: 1px solid #1f8f45;
                min-width: 140px;
            }

            QPushButton#successOutlineButton:hover {
                background: #edf9f0;
                color: #1f8f45;
            }

            QFrame#queryBuilderFrame {
                background: #f7f7f9;
                border: 1px solid #d8dbe3;
                border-radius: 8px;
            }

            QProgressBar {
                border: 1px solid #c5cbd8;
                border-radius: 6px;
                text-align: center;
                height: 20px;
                background: white;
            }

            QProgressBar::chunk {
                background-color: #1b8f1b;
                border-radius: 5px;
            }

            QFrame#archiveSourceFrame {
                background: #ffffff;
                border: 1px solid #d8dbe3;
                border-left: 4px solid #7b61ff;
                border-radius: 10px;
            }

            QLabel#archiveSourceLabel {
                color: #0b1437;
                font-size: 11pt;
                font-weight: 700;
            }

            QLabel#archiveSourceHint {
                color: #7a8191;
                font-size: 9pt;
            }

            QComboBox#archiveSourceMode {
                background: #f7f4ff;
                color: #3d2bb8;
                border: 1px solid #a997ff;
                border-radius: 8px;
                padding: 7px 34px 7px 12px;
                min-width: 160px;
                font-weight: 600;
            }

            QComboBox#archiveSourceMode:hover,
            QComboBox#archiveSourceMode:on {
                background: #f0ebff;
                border-color: #7b61ff;
            }

            QComboBox#archiveSourceMode::drop-down {
                width: 28px;
                border: none;
                border-left: 1px solid #d9d0ff;
            }

            QComboBox#archiveSourceMode QAbstractItemView {
                background: white;
                color: #0b1437;
                border: 1px solid #d8dbe3;
                border-radius: 8px;
                padding: 4px;
                selection-background-color: #f0ebff;
                selection-color: #3d2bb8;
                outline: none;
            }

            QComboBox#metadataImportSelector {
                background: #effaf3;
                color: #167443;
                border: 1px solid #66b989;
                border-radius: 8px;
                padding: 7px 34px 7px 12px;
                min-width: 220px;
                font-weight: 600;
            }

            QComboBox#metadataImportSelector:hover,
            QComboBox#metadataImportSelector:on {
                background: #e1f5e8;
                border-color: #2c925c;
            }

            QComboBox#metadataImportSelector::drop-down {
                width: 28px;
                border: none;
                border-left: 1px solid #b9e3c8;
            }

            QComboBox#metadataImportSelector QAbstractItemView {
                background: white;
                color: #0b1437;
                border: 1px solid #b9d9c5;
                border-radius: 8px;
                padding: 4px;
                selection-background-color: #e1f5e8;
                selection-color: #167443;
                outline: none;
            }

            QLineEdit, QTextEdit, QSpinBox, QComboBox, QDateTimeEdit {
                background: white;
                padding: 6px;
                border: 1px solid #d8dbe3;
                border-radius: 8px;
            }


            QFrame#analyticsNavFrame, QFrame#analyticsDetailFrame {
                background: white;
                border: 1px solid #d8dbe3;
                border-radius: 10px;
            }

            QListWidget#analyticsMenu {
                background: white;
                border: none;
                outline: none;
                padding: 4px;
            }

            QListWidget#analyticsMenu::item {
                padding: 10px 12px;
                border-radius: 8px;
                color: #0b1437;
                margin: 2px 4px;
            }

            QListWidget#analyticsMenu::item:selected {
                background: #eef4ff;
                color: #0b1437;
                border: 1px solid #c9dafc;
            }

            QListWidget#analyticsMenu::item:hover {
                background: #f3f6fb;
            }
            """
        )


def _close_pyinstaller_splash() -> None:
    """Close the PyInstaller --splash window as soon as Qt can process events."""
    try:
        import pyi_splash  # type: ignore[import-not-found]
    except ImportError:
        return
    try:
        pyi_splash.close()
    except Exception:
        pass


def main() -> int:
    app = QApplication([])
    app.setOrganizationName(APP_ORG)
    app.setApplicationName(APP_NAME)
    # PyInstaller's bootloader splash is not a Qt window and cannot be
    # minimized. Close it immediately once the Qt application exists, rather
    # than leaving it fixed on screen while the main window is constructed.
    _close_pyinstaller_splash()
    window = MainWindow()
    window.show()
    return app.exec()


if __name__ == "__main__":
    raise SystemExit(main())
