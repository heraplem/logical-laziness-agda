"""Clean BibTeX link/url fields when DOI is present.

This script scans `.bib` files recursively and removes `link` and `url`
fields from entries that already contain a `doi` field.
"""

from __future__ import annotations

import argparse
import shutil
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence


@dataclass(frozen=True)
class FieldSpan:
    """A single BibTeX field location inside an entry."""

    name: str
    start: int
    end: int


@dataclass(frozen=True)
class BibEntrySpan:
    """Parsed structure of a BibTeX entry."""

    start: int
    end: int
    fields: tuple[FieldSpan, ...]


@dataclass(frozen=True)
class EntryResult:
    """Result of rewriting one BibTeX entry."""

    modified: bool
    removed_fields: int


@dataclass(frozen=True)
class FileResult:
    """Result of processing one BibTeX file."""

    path: Path
    modified: bool
    entries_modified: int
    fields_removed: int


@dataclass(frozen=True)
class FieldRemovalResult:
    """Aggregate cleanup counters for one script run."""

    files_scanned: int
    files_changed: int
    entries_modified: int
    fields_removed: int


def _is_escaped(text: str, index: int) -> bool:
    """Return whether the character at `index` is escaped by backslashes."""

    backslashes = 0
    cursor = index - 1
    while cursor >= 0 and text[cursor] == "\\":
        backslashes += 1
        cursor -= 1
    return (backslashes % 2) == 1


def _find_matching_delimiter(
    text: str, open_index: int, open_char: str, close_char: str
) -> int:
    """Return the exclusive end index of a balanced delimiter span."""

    depth = 1
    in_quote = False
    cursor = open_index + 1
    while cursor < len(text):
        char = text[cursor]
        if char == '"' and not _is_escaped(text, cursor):
            in_quote = not in_quote
        elif not in_quote:
            if char == open_char:
                depth += 1
            elif char == close_char:
                depth -= 1
                if depth == 0:
                    return cursor + 1
        cursor += 1
    raise ValueError(f"Unbalanced BibTeX entry starting at index {open_index}")


def _find_top_level_char(
    text: str, start: int, end: int, target: str
) -> int | None:
    """Find `target` between start/end while ignoring nested braces/parens/quotes."""

    brace_depth = 0
    paren_depth = 0
    in_quote = False

    for cursor in range(start, end):
        char = text[cursor]
        if char == '"' and not _is_escaped(text, cursor):
            in_quote = not in_quote
            continue
        if in_quote:
            continue
        if char == "{":
            brace_depth += 1
        elif char == "}":
            brace_depth = max(0, brace_depth - 1)
        elif char == "(":
            paren_depth += 1
        elif char == ")":
            paren_depth = max(0, paren_depth - 1)
        elif char == target and brace_depth == 0 and paren_depth == 0:
            return cursor
    return None


def _find_field_end(text: str, value_start: int, entry_inner_end: int) -> int:
    """Find the end index of a field value, including trailing comma when present."""

    brace_depth = 0
    paren_depth = 0
    in_quote = False

    cursor = value_start
    while cursor < entry_inner_end:
        char = text[cursor]
        if char == '"' and not _is_escaped(text, cursor):
            in_quote = not in_quote
        elif not in_quote:
            if char == "{":
                brace_depth += 1
            elif char == "}":
                brace_depth = max(0, brace_depth - 1)
            elif char == "(":
                paren_depth += 1
            elif char == ")":
                paren_depth = max(0, paren_depth - 1)
            elif char == "," and brace_depth == 0 and paren_depth == 0:
                return cursor + 1
        cursor += 1
    return entry_inner_end


def _parse_entry_fields(entry_text: str) -> BibEntrySpan:
    """Parse fields and spans for one full BibTeX entry text."""

    if not entry_text.startswith("@"):
        raise ValueError("Entry text must start with '@'")

    cursor = 1
    while cursor < len(entry_text) and (
        entry_text[cursor].isalpha() or entry_text[cursor] in {"-", "_"}
    ):
        cursor += 1
    while cursor < len(entry_text) and entry_text[cursor].isspace():
        cursor += 1

    if cursor >= len(entry_text) or entry_text[cursor] not in {"{", "("}:
        raise ValueError("Invalid BibTeX entry header")

    open_char = entry_text[cursor]
    close_char = "}" if open_char == "{" else ")"
    if entry_text[-1] != close_char:
        raise ValueError("Entry boundary mismatch")

    inner_start = cursor + 1
    inner_end = len(entry_text) - 1
    first_comma = _find_top_level_char(entry_text, inner_start, inner_end, ",")
    if first_comma is None:
        return BibEntrySpan(0, len(entry_text), ())

    fields: list[FieldSpan] = []
    field_cursor = first_comma + 1
    while field_cursor < inner_end:
        whitespace_start = field_cursor
        while field_cursor < inner_end and entry_text[field_cursor].isspace():
            field_cursor += 1
        if field_cursor >= inner_end:
            break
        if entry_text[field_cursor] == ",":
            field_cursor += 1
            continue

        field_start = whitespace_start
        equals_index = _find_top_level_char(entry_text, field_cursor, inner_end, "=")
        if equals_index is None:
            break

        name = entry_text[field_cursor:equals_index].strip().lower()
        field_end = _find_field_end(entry_text, equals_index + 1, inner_end)
        if name:
            fields.append(FieldSpan(name=name, start=field_start, end=field_end))
        field_cursor = field_end

    return BibEntrySpan(0, len(entry_text), tuple(fields))


def rewrite_entry_if_needed(entry_text: str) -> tuple[str, EntryResult]:
    """Remove link/url fields from one entry if it contains a DOI."""

    entry = _parse_entry_fields(entry_text)
    has_doi = any(field.name == "doi" for field in entry.fields)
    if not has_doi:
        return entry_text, EntryResult(modified=False, removed_fields=0)

    removable_fields = [
        field for field in entry.fields if field.name in {"link", "url"}
    ]
    if not removable_fields:
        return entry_text, EntryResult(modified=False, removed_fields=0)

    rewritten = entry_text
    for field in sorted(removable_fields, key=lambda span: span.start, reverse=True):
        rewritten = rewritten[: field.start] + rewritten[field.end :]
    return rewritten, EntryResult(modified=True, removed_fields=len(removable_fields))


def _find_bib_entry_ranges(text: str) -> list[tuple[int, int]]:
    """Locate BibTeX entry start/end ranges in a file."""

    ranges: list[tuple[int, int]] = []
    cursor = 0
    while cursor < len(text):
        at_index = text.find("@", cursor)
        if at_index == -1:
            break

        probe = at_index + 1
        while probe < len(text) and text[probe].isspace():
            probe += 1
        while probe < len(text) and (text[probe].isalpha() or text[probe] in {"-", "_"}):
            probe += 1
        while probe < len(text) and text[probe].isspace():
            probe += 1

        if probe >= len(text) or text[probe] not in {"{", "("}:
            cursor = at_index + 1
            continue

        open_char = text[probe]
        close_char = "}" if open_char == "{" else ")"
        end_index = _find_matching_delimiter(text, probe, open_char, close_char)
        ranges.append((at_index, end_index))
        cursor = end_index

    return ranges


def find_bib_files(root: Path) -> list[Path]:
    """Return all `.bib` files under `root` in deterministic order."""

    return sorted(path for path in root.rglob("*.bib") if path.is_file())


def _atomic_write_text(path: Path, content: str) -> None:
    """Atomically write UTF-8 text to `path` using a temporary sibling file."""

    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        dir=path.parent,
        prefix=f".{path.name}.",
        suffix=".tmp",
        delete=False,
    ) as handle:
        tmp_path = Path(handle.name)
        handle.write(content)
        handle.flush()

    tmp_path.replace(path)


def process_bib_file(
    path: Path, *, dry_run: bool, backup: bool, verbose: bool
) -> FileResult:
    """Process one `.bib` file and optionally write cleaned content."""

    content = path.read_text(encoding="utf-8")
    entry_ranges = _find_bib_entry_ranges(content)

    rebuilt_parts: list[str] = []
    cursor = 0
    entries_modified = 0
    fields_removed = 0

    for start, end in entry_ranges:
        rebuilt_parts.append(content[cursor:start])
        original_entry = content[start:end]
        rewritten_entry, entry_result = rewrite_entry_if_needed(original_entry)
        rebuilt_parts.append(rewritten_entry)
        cursor = end

        if entry_result.modified:
            entries_modified += 1
            fields_removed += entry_result.removed_fields

    rebuilt_parts.append(content[cursor:])
    rewritten_content = "".join(rebuilt_parts)
    modified = rewritten_content != content

    if verbose:
        print(
            f"{path}: entries={len(entry_ranges)}, "
            f"entries_modified={entries_modified}, fields_removed={fields_removed}"
        )

    if modified and not dry_run:
        if backup:
            backup_path = path.with_suffix(f"{path.suffix}.bak")
            shutil.copy2(path, backup_path)
        _atomic_write_text(path, rewritten_content)

    return FileResult(
        path=path,
        modified=modified,
        entries_modified=entries_modified,
        fields_removed=fields_removed,
    )


def _parse_args(argv: Sequence[str] | None) -> argparse.Namespace:
    """Parse CLI arguments for the cleanup script."""

    parser = argparse.ArgumentParser(
        description=(
            "Remove link/url fields from BibTeX entries when a doi field is present."
        )
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("."),
        help="Root directory to scan recursively for .bib files (default: current dir).",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Report changes without writing files.",
    )
    parser.add_argument(
        "--no-backup",
        action="store_true",
        help="Disable .bak backup creation before rewriting files.",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print per-file processing details.",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    """Run the CLI and return a process exit code."""

    args = _parse_args(argv)
    files = find_bib_files(args.root)
    totals = FieldRemovalResult(
        files_scanned=len(files),
        files_changed=0,
        entries_modified=0,
        fields_removed=0,
    )

    had_error = False
    for path in files:
        try:
            result = process_bib_file(
                path=path,
                dry_run=args.dry_run,
                backup=not args.no_backup,
                verbose=args.verbose,
            )
        except (OSError, ValueError) as exc:
            print(f"Error processing {path}: {exc}", file=sys.stderr)
            had_error = True
            continue

        totals = FieldRemovalResult(
            files_scanned=totals.files_scanned,
            files_changed=totals.files_changed + int(result.modified),
            entries_modified=totals.entries_modified + result.entries_modified,
            fields_removed=totals.fields_removed + result.fields_removed,
        )

    print(
        "Summary: "
        f"files_scanned={totals.files_scanned}, "
        f"files_changed={totals.files_changed}, "
        f"entries_modified={totals.entries_modified}, "
        f"fields_removed={totals.fields_removed}"
    )
    return 1 if had_error else 0


if __name__ == "__main__":
    raise SystemExit(main())
