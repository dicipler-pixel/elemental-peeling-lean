#!/usr/bin/env bash
# Build "One Body": redraw the figure from the shipped archive, then typeset the paper.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/band_figure.py
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error one-body.tex
latexmk -c one-body.tex > /dev/null 2>&1 || true
echo "built paper/one-body.pdf"
