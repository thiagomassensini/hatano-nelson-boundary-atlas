# Hatano–Nelson Boundary Atlas v0.1.0

Initial Lean 4 release of the finite algebraic layer behind diagonal gauge
removal and boundary compression in Hatano–Nelson systems.

## Diagonal gauge covariance

For a nowhere-zero vertex dressing `d`, the formalization defines

```math
H^{(d)}_{ij}=d_i^{-1}H_{ij}d_j
```

and proves that this is exactly

```math
\operatorname{diag}(d^{-1})\,H\,\operatorname{diag}(d).
```

Successive dressings multiply pointwise, diagonal entries stay fixed, and the
matrix zero pattern is preserved.

## Carrier holonomy

Multiplicative edge carriers transform by the same vertex dressing. The
carrier product along an open path changes only by endpoint factors. Closing
the path cancels those factors exactly, so every closed-walk holonomy is gauge
invariant. A pure vertex gauge therefore has unit holonomy.

## Discrete Green identity

For the symmetric bilinear pairing, Lean proves

```math
\langle Hu,v\rangle-\langle u,Hv\rangle
=
\langle v,(H-H^\mathsf{T})u\rangle.
```

Thus the Green defect vanishes for every symmetric bulk operator.

## Boundary compression

For a boundary map `B` and boundary matrix `Δ`, define

```math
H=H_0+B^\mathsf{T}\Delta B.
```

The release proves the exact identity

```math
H-H^\mathsf{T}
=
(H_0-H_0^\mathsf{T})
+
B^\mathsf{T}(\Delta-\Delta^\mathsf{T})B.
```

When the bulk is symmetric, the whole irreducible Green defect is carried by
the finite boundary atlas. Vertices invisible to `B` have zero rows and
columns in the lifted correction.

## Certified surface

The public root exports 32 theorems and 11 definitions or abbreviations across
four modules:

- `HatanoNelsonBoundaryAtlas.Gauge`;
- `HatanoNelsonBoundaryAtlas.Holonomy`;
- `HatanoNelsonBoundaryAtlas.Green`;
- `HatanoNelsonBoundaryAtlas.BoundaryCompression`.

## Scope

This release contains finite algebraic statements only. It does not claim a
localization transition, a universal Lyapunov criterion, a continuum limit, a
mobility edge, or a numerical scaling law.

CI builds with `lake build --wfail`, rejects proof placeholders and
project-specific axioms, and recompiles the public root directly.
