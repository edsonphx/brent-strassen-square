# Release v1.0.0

The source tree and its public archive contain the same version of the paper,
verifier, and frozen data. Run `bash verify.sh` first.

1. Publish the repository under `edsonphx/brent-strassen-square` and push its
   default branch. Check that GitHub renders the citation metadata.
2. In [Zenodo GitHub settings](https://zenodo.org/account/settings/github/),
   link the GitHub account and enable this specific repository. Zenodo uses
   the root `.zenodo.json` for the archived record.
3. Push the `v1.0.0` tag. On the intended repository the bundled GitHub
   Actions workflow verifies the tagged tree and creates the release with the
   PDF and ZIP attached. If Actions is unavailable, create the regular
   release from the same tag in GitHub and attach both files.
4. Check that Zenodo processed the release. Use the version DOI shown on
   the public Zenodo record in citations.

See [Zenodo's GitHub release guide](https://help.zenodo.org/docs/github/archive-software/github-upload/).
