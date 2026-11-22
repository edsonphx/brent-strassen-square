# Release and archive

The GitHub release and Zenodo archive preserve tagged snapshots of the
preprint, its source, the verification data, and the verifier.

1. Compile the PDF and regenerate the SHA-256 manifest. Run
   `bash verify.sh --full` from a clean copy of the release candidate.
2. Set the candidate version in the preprint, `CITATION.cff`,
   `.zenodo.json`, and the release workflow. Zenodo reads the
   catalogue metadata from `.zenodo.json`.
3. Push the commit and its version tag. The tag triggers GitHub Actions
   to verify the snapshot and publish a regular release with the PDF
   and a ZIP attached. The repository is linked in
   [Zenodo's GitHub settings](https://zenodo.org/account/settings/github/).
4. Confirm that Zenodo archived the release as a new version. The
   [concept DOI](https://doi.org/10.5281/zenodo.24449375) resolves to
   the latest archived version. Cite the version DOI when referencing
   specific files.

The original snapshot is [version 1.0.0](https://doi.org/10.5281/zenodo.24449376).
See [Zenodo's GitHub release guide](https://help.zenodo.org/docs/github/archive-software/github-upload/)
for processing and troubleshooting.
