#!/usr/bin/env bash
# build_paper.sh -- build the paper and the release files.
#
#   dist/SimpsonCircularAbelianSquares_final2.pdf             the paper
#   dist/SimpsonCircularAbelianSquares_final2-tex.zip         LaTeX source with the figures as PNG
#   dist/SimpsonCircularAbelianSquares_final2-arxiv.tar.gz    the same source as an arXiv tarball
#   preprintSimpsonCircularAbelianSquares/SimpsonCircularAbelianSquares.pdf
#                                                             the paper (the only file there)
#   MasterSimpsonCircularAbelianSquares_masterzipfinal2.zip   every tracked file with dist/ and
#                                                             the preprint folder
#
# Needs pdflatex, git, zip and tar.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
for t in pdflatex zip tar git; do
  command -v "$t" >/dev/null || { echo "missing tool: $t" >&2; exit 2; }
done

NAME=SimpsonCircularAbelianSquares
PRE=preprint$NAME
MASTER=Master${NAME}_masterzipfinal2.zip

latex() { pdflatex -interaction=nonstopmode -halt-on-error "$@" > /dev/null; }

echo "== paper"
cd "$ROOT/paper"
rm -f main.aux main.out
for run in 1 2 3 4; do
  latex main.tex
  grep -q "Rerun to get" main.log || break
done
if grep -q "Overfull\|Underfull\|undefined\|Rerun to get" main.log; then
  grep "Overfull\|Underfull\|undefined\|Rerun to get" main.log
  echo "build_paper.sh: fix the warnings above" >&2
  exit 1
fi
rm -f main.aux main.log main.out
cd "$ROOT"

rm -rf dist
mkdir -p dist "$PRE"
cp paper/main.pdf "dist/${NAME}_final2.pdf"
cp paper/main.pdf "$PRE/$NAME.pdf"
mkdir -p paper/paper1 paper/paper2
cp paper/main.pdf "paper/paper1/$NAME.pdf"

STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT

echo "== tex zip and arXiv tarball"
SRC="$STAGE/${NAME}_final2-tex"
mkdir -p "$SRC/figures"
cp paper/main.tex paper/elsarticle.cls "$SRC/"
cp paper/figures/*.png "$SRC/figures/"
( cd "$STAGE" && zip -qrX "${NAME}_final2-tex.zip" "${NAME}_final2-tex" )
mv "$STAGE/${NAME}_final2-tex.zip" dist/
cp "dist/${NAME}_final2-tex.zip" "paper/paper2/${NAME}-tex.zip"
tar -czf "dist/${NAME}_final2-arxiv.tar.gz" -C "$SRC" main.tex elsarticle.cls figures

echo "== $MASTER"
mkdir -p "$STAGE/master/Master$NAME"
git ls-files -z | grep -zvE "^(dist/|$PRE/|$MASTER\$)" \
  | while IFS= read -r -d '' f; do
      [ -e "$f" ] || continue
      mkdir -p "$STAGE/master/Master$NAME/$(dirname "$f")"
      cp -p "$f" "$STAGE/master/Master$NAME/$f"
    done
mkdir -p "$STAGE/master/Master$NAME/dist" "$STAGE/master/Master$NAME/$PRE"
cp dist/* "$STAGE/master/Master$NAME/dist/"
cp "$PRE/$NAME.pdf" "$STAGE/master/Master$NAME/$PRE/"
rm -f "$MASTER"
( cd "$STAGE/master" && zip -qrX "$ROOT/$MASTER" "Master$NAME" )

echo "built: $(ls dist | tr '\n' ' ')$PRE/$NAME.pdf $MASTER"
