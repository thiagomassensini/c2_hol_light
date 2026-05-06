# C2 HOL Light

HOL Light formalization of the main layers of the C2 route, including the
branch barrier, the residual/transfer chain, `c0` normalization, the
continuation interface, the meromorphic bridge, transversality, and the
off-axis Taylor-dominance endpoint.

## Verification

For a short verification of the current state:

```bash
bash run_c2_full_chain.sh
bash run_c2_meromorphic_ext.sh
bash run_c2_public_api.sh
```

## Main Files

- `c2_full_chain.ml` packages the off-axis endpoint.
- `c2_meromorphic_ext.ml` contains the current meromorphic bridge.
- `c2_public_api.ml` exposes the public HOL-facing surface.
- `REPORT.md` summarizes the current formal inventory.

## Citation

Citation and release metadata are provided in `CITATION.cff`, `.zenodo.json`,
and `ZENODO_RELEASE_2026-05-06.1.md`.
