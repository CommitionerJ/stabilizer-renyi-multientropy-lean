"""Read-only release integrity check. Python >= 3.11; no Lean/Lake calls."""

import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import sys

if sys.version_info < (3, 11):
    raise SystemExit("Requires Python >= 3.11; alternatively use shasum -a 256 -c SHA256SUMS")

import tomllib


ROOT = Path(__file__).resolve().parent
PACKAGES = {
    "Core2": ("Core2", 2, 850),
    "Core3": ("Core3tree", 2, 6365),
    "TreeGraph": ("TreeGraph", 154, 105384),
    "Core3loop": ("Core3loop", 45, 31227),
    "Core4loop": ("Core4loop", 432, 177042),
}
MATHLIB_REV = "8a178386ffc0f5fef0b77738bb5449d50efeea95"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest(name, expected):
    seen = set()
    for row in (ROOT / name).read_text(encoding="utf-8").splitlines():
        value, relative = row.split("  ", 1)
        parts = PurePosixPath(relative)
        require(not parts.is_absolute() and ".." not in parts.parts,
                f"Unsafe manifest path: {relative}")
        require(relative not in seen, f"Duplicate manifest entry: {relative}")
        require(relative in expected, f"Unexpected manifest entry: {relative}")
        require(digest(ROOT / relative) == value, f"Hash mismatch: {relative}")
        seen.add(relative)
    require(seen == expected, f"Incomplete manifest: {name}")
    print(f"PASS {name}: {len(seen)} files")


def main():
    entries = []
    for directory, subdirs, names in os.walk(ROOT, followlinks=False):
        base = Path(directory)
        if base == ROOT:
            subdirs[:] = [name for name in subdirs if name != ".git"]
            names = [name for name in names if name != ".git"]
        entries.extend(base / name for name in subdirs + names)
    require(not any(p.is_symlink() for p in entries), "Symlink in release")
    allowed_dotfiles = {ROOT / ".gitignore", ROOT / ".gitattributes"}
    require(not any((p.name.startswith(".") and p not in allowed_dotfiles)
                    or p.name == "__pycache__" for p in entries),
            "Unexpected hidden metadata or cache in release")
    files = {p.relative_to(ROOT).as_posix() for p in entries if p.is_file()}
    require(not any(Path(p).suffix.lower() in
                    {".olean", ".ilean", ".o", ".a", ".so", ".dylib", ".pyc", ".md"}
                    for p in files), "Unexpected build or Markdown artifact")
    require(len({p.casefold() for p in files}) == len(files),
            "Case-colliding file paths")
    lean = {p for p in files if p.endswith(".lean")}
    require(len(lean) == 635, "Unexpected Lean source count")
    check_manifest("SHA256SUMS", files - {"SHA256SUMS"})
    check_manifest("PROOF_SOURCE_SHA256SUMS", lean)
    for folder, (package, file_count, line_count) in PACKAGES.items():
        base = ROOT / folder
        config = tomllib.loads((base / "lakefile.toml").read_text())
        manifest = json.loads((base / "lake-manifest.json").read_text())
        require(config["name"] == manifest["name"] == package,
                f"Package name mismatch: {folder}")
        require((base / "lean-toolchain").read_text().strip() ==
                "leanprover/lean4:v4.29.0", f"Toolchain mismatch: {folder}")
        mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
        requested = next(p for p in config["require"] if p["name"] == "mathlib")
        require(requested["rev"] == mathlib["rev"] == mathlib["inputRev"] ==
                MATHLIB_REV, f"mathlib revision mismatch: {folder}")
        project_files = [p for p in lean if p.startswith(folder + "/")]
        lines = sum((ROOT / p).read_bytes().count(b"\n") for p in project_files)
        require(len(project_files) == file_count and lines == line_count,
                f"Source inventory mismatch: {folder}")
        if folder == "Core4loop":
            sibling = next(p for p in config["require"] if p["name"] == "Core3loop")
            locked = next(p for p in manifest["packages"] if p["name"] == "Core3loop")
            require(sibling["path"] == locked["dir"] == "../Core3loop",
                    "Core4loop sibling dependency mismatch")
        print(f"PASS {folder}: metadata, {file_count} Lean files, {lines} lines")
    print("PASS release integrity; no compilation or mathematical certification performed")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, StopIteration) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
