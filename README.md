# Hatano–Nelson Boundary Atlas

Lean 4 formalization of finite-dimensional gauge and boundary identities
underlying Hatano–Nelson systems.

The first checkpoint isolates four exact algebraic layers:

- diagonal vertex-gauge covariance;
- closed-walk holonomy invariance;
- the finite discrete Green identity;
- compression of every boundary Green defect through `Bᵀ * Δ * B`.

The certified statements do not assert a localization transition, a universal
Lyapunov threshold, a continuum limit, or a numerical mobility edge.

## Modules

- `HatanoNelsonBoundaryAtlas/Gauge.lean`
- `HatanoNelsonBoundaryAtlas/Holonomy.lean`
- `HatanoNelsonBoundaryAtlas/Green.lean`
- `HatanoNelsonBoundaryAtlas/BoundaryCompression.lean`

See [`docs/FORMALIZATION.md`](docs/FORMALIZATION.md) for the theorem map.

## Verification

CI builds with `lake build --wfail`, rejects proof placeholders and
project-specific axioms, and recompiles the public root directly.

## License

Apache-2.0.
