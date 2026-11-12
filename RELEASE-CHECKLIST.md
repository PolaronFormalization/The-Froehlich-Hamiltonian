# Final publication checklist

- [x] Restore the **original** `GW.lean` full-import entry point, unchanged.
- [x] Restore the **original** `lake-manifest.json` lockfile, unchanged.
- [x] Keep exact original `lean-toolchain` and Mathlib revision.
- [x] Confirm every public mathematical proof source matches the uploaded completed development byte-for-byte (except the excluded development-only `GW/Verification.lean`).
- [x] Replace the nonportable development verification target with standalone public proof/axiom checks.
- [ ] **On the Mac, extract into a new directory** and run `lake exe cache get && bash scripts/check.sh`; do not use the old project checkout as a substitute.
- [ ] Verify GitHub Actions succeeds on a fresh checkout after push.
- [ ] Choose and add an appropriate source-code license, with any required third-party notices.
- [ ] Confirm redistributability of `source/GW-paper-formalization.tex` and appropriate acknowledgments.
- [ ] Set authorship/citation metadata (`CITATION.cff`), if desired.

This is a source-only **release candidate** until its own clean installation and checks complete.
