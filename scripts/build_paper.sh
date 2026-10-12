#!/usr/bin/env bash
# build_paper.sh -- build the paper and the release files into dist/.
#
#   dist/simpson-abelian-squares.pdf              the compiled paper
#   dist/simpson-abelian-squares-tex.zip          LaTeX source (main.tex, elsarticle.cls)
#   dist/simpson-abelian-squares-arxiv.tar.gz     the same source, ready for arXiv
#   dist/MasterSimpsonCircularAbelianSquaresZip.zip
#                                                 every file of the repository with the three
#                                                 files above, in the folder
#                                                 MasterSimpsonCircularAbelianSquaresZip/
#
# Needs pdflatex, git, zip and tar.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PAPER="$ROOT/paper"
DIST="$ROOT/dist"
NAME=simpson-abelian-squares
MASTER=MasterSimpsonCircularAbelianSquaresZip
mkdir -p "$DIST"

latex() { pdflatex -interaction=nonstopmode -halt-on-error "$@" > /dev/null; }

echo "== paper"
cd "$PAPER"
latex main.tex
latex main.tex
if grep -q "Overfull\|Underfull\|undefined\|Rerun to get" main.log; then
  grep "Overfull\|Underfull\|undefined\|Rerun to get" main.log
  echo "build_paper.sh: fix the warnings above" >&2
  exit 1
fi
rm -f main.aux main.log main.out
cp main.pdf "$DIST/$NAME.pdf"

STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT

echo "== tex.zip"
mkdir -p "$STAGE/$NAME"
cp main.tex elsarticle.cls "$STAGE/$NAME/"
rm -f "$DIST/$NAME-tex.zip"
( cd "$STAGE" && zip -qrX "$DIST/$NAME-tex.zip" "$NAME" )

echo "== arXiv tarball"
mkdir -p "$STAGE/arxiv"
cp main.tex elsarticle.cls "$STAGE/arxiv/"
( cd "$STAGE/arxiv" && latex main.tex && latex main.tex && rm -f main.aux main.log main.out main.pdf )
tar -czf "$DIST/$NAME-arxiv.tar.gz" -C "$STAGE/arxiv" main.tex elsarticle.cls

echo "== $MASTER.zip"
cd "$ROOT"
mkdir -p "$STAGE/master/$MASTER"
git ls-files --cached --others --exclude-standard -z \
  | grep -zv "^dist/$MASTER.zip\$" \
  | while IFS= read -r -d '' f; do
      [ -e "$f" ] || continue
      mkdir -p "$STAGE/master/$MASTER/$(dirname "$f")"
      cp -p "$f" "$STAGE/master/$MASTER/$f"
    done
mkdir -p "$STAGE/master/$MASTER/dist"
cp "$DIST/$NAME.pdf" "$DIST/$NAME-tex.zip" "$DIST/$NAME-arxiv.tar.gz" "$STAGE/master/$MASTER/dist/"
rm -f "$DIST/$MASTER.zip"
( cd "$STAGE/master" && zip -qrX "$DIST/$MASTER.zip" "$MASTER" )

ls -l "$DIST"
