# CLAUDE.md

Guidance for Claude Code sessions (local and cloud) working in this repository.

## Build

These mirror CI (`.github/workflows/build.yml`):

- `lake --keep-toolchain build --wfail` builds the library; warnings are errors.
- `cd util && lake --keep-toolchain --update --wfail build` builds the table
  generators and `TestTables`, which checks the lookup tables against
  `lean4-unicode-data`.
- `cd docs && lake build --keep-toolchain UnicodeBasic:docs` builds the docs.

## Rules

- Stay dependency-free: do not add Batteries, Mathlib or any other `require`
  to the main package. (`util/` and `docs/` are separate packages and may
  have dependencies.)
- Never put Claude session links in commit messages or PR descriptions: no
  `claude.ai/code/session_...` URLs, no `Claude-Session:` trailers, no
  project or thread links. Strip any footer a tool adds automatically.
- Versions exist only as git tags on `main` (`vX.Y.Z`); there is no version
  file. After an update to a new stable Lean release merges, push the next
  patch tag on that merge commit (pushing a tag runs `release.yml`). Release
  candidate updates do not bump the version, and existing tags are never
  moved.
- Toolchain update PRs are opened automatically by
  `update-toolchain.yml`; prefer fixing those over opening new ones.
