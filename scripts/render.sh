#!/usr/bin/env bash

set -e
sh scripts/generate-everything.sh
trap "rm -f Everything.agda" 0 2 3 15
agda --version
agda --html --html-dir=docs Everything.agda
cp style.css docs/Agda.css
