#!/usr/bin/env bash

set -euo pipefail

lake build LeanModularForms.Blueprint
lake env lean --run LeanModularFormsMain.lean --output _out/site

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-preview-manifest.json
