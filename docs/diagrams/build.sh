#!/usr/bin/env bash
# Compile every TikZ diagram in this directory to an SVG in ../static/.
# Requires pdflatex (TeX Live) and pdftocairo (poppler-utils).
set -euo pipefail
cd "$(dirname "$0")"
out=../static
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
for tex in *.tex; do
  [ "$tex" = style.tex ] && continue
  name=${tex%.tex}
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory "$tmp" "$tex" >/dev/null
  pdftocairo -svg "$tmp/$name.pdf" "$out/$name.svg"
  echo "built $out/$name.svg"
done
