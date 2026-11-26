#!/usr/bin/env bash
# Pack the Mac build of the LWH certificates for CI, which cannot compile them (runner memory).
# Run from lean/ after `lake build Brent.LWH` succeeds. Upload the tarball as an asset of the
# GitHub release named in BUILD.txt, then commit BUILD.txt.
set -euo pipefail
commit=$(git rev-parse --short HEAD)
out="lwh-build-${commit}.tar.gz"
tar -czf "$out" .lake/build
sha=$(shasum -a 256 "$out" | cut -d' ' -f1)
printf 'tag=lwh-build-%s\nasset=%s\nsha256=%s\nsource_commit=%s\n' "$commit" "$out" "$sha" "$(git rev-parse HEAD)" > tools/lwh/BUILD.txt
echo "created $out ($sha); upload with:"
echo "  gh release create lwh-build-$commit $out --prerelease --title 'LWH build $commit' --notes 'Mac build of Brent.LWH for CI kernel replay'"
