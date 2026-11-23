#!/usr/bin/env bash
# Build the paper's PDF from its Markdown source. Needs pandoc + xelatex (both present in the VM).
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/paper-inventory.py > /dev/null
pandoc results/light-bridge-paper.md \
  -o paper/light-bridge-paper.pdf \
  --pdf-engine=xelatex \
  -V geometry:margin=2.4cm \
  -V fontsize=10pt \
  -V mainfont="DejaVu Serif" \
  -V monofont="DejaVu Sans Mono" \
  -V colorlinks=true \
  --toc --toc-depth=1
echo "built paper/light-bridge-paper.pdf"
