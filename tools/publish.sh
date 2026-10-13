#!/bin/sh
# Verify, build, and publish to both hosts. Nothing is published unless every check passes.
#   sh tools/publish.sh "what changed"
set -e
cd "$(dirname "$0")/.."
[ -n "$1" ] || { echo "usage: sh tools/publish.sh \"what changed\""; exit 1; }
sh tools/verify.sh
node tools/build.mjs
git add -A && git commit -m "$1"
git push origin main
sh tools/deploy-mirror.sh
