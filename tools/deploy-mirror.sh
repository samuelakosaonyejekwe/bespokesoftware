#!/bin/sh
# Publishes the same static files to the second host (Cloudflare Pages), independent of the first.
#   sh tools/deploy-mirror.sh
set -e
cd "$(dirname "$0")/.."
node tools/build.mjs
out=$(mktemp -d)
cp -r index.html manifest.webmanifest config.json sw.js bespoke-offline.zip css js vendor icons functions "$out"/
# the server function and its language-model binding are declared in wrangler.toml; it is deployed from the copy
cp wrangler.toml "$out"/
(cd "$out" && npx --yes wrangler@3 pages deploy . --project-name "${MIRROR_PROJECT:-bespokesoftware}" --branch "${MIRROR_BRANCH:-main}" --commit-dirty=true)
rm -rf "$out"
