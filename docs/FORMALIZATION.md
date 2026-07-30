# Formalization map

## Scope

The library certifies finite algebraic identities motivated by the first three
Hatano–Nelson exploration notebooks. The physical terminology records
provenance; no spectral threshold, continuum convergence, localization law, or
numerical classification is imported into the theorem statements.

All declarations are exported by `HatanoNelsonBoundaryAtlas.lean`.

## 1. Diagonal vertex gauge

### Definitions

```lean
diagonalGauge
EdgeCarrier
carrierGauge
carrierMatrix
```

The matrix action is

```math
H_{ij}\longmapsto d_i^{-1}H_{ij}d_j.
```

### Theorems

```lean
diagonalGauge_apply
diagonalGauge_one
diagonalGauge_comp
diagonalGauge_eq_diagonal_mul
diagonalGauge_diagonal
diagonalGauge_eq_zero_iff
carrierGauge_apply
carrierMatrix_apply
carrierMatrix_carrierGauge
carrierGauge_eq_zero_iff
```

The carrier formulation separates reciprocal hopping amplitudes from the
multiplicative gauge data. No logarithm or exponential is required.

## 2. Closed-walk holonomy

### Definitions

```lean
pathCarrier
lastVertex
cycleCarrier
```

### Theorems

```lean
pathCarrier_carrierGauge
cycleCarrier_carrierGauge
pathCarrier_one
cycleCarrier_one
pureGauge_cycleCarrier
```

For an open path from `s` to `t`, carrier dressing produces only the endpoint
factor

```math
d_s^{-1}d_t.
```

Closing the path cancels it, proving exact gauge invariance of the cycle
product.

## 3. Finite Green identity

### Definitions

```lean
greenMatrix
greenForm
```

The sign convention is

```math
\operatorname{Green}(H)=H-H^\mathsf{T}.
```

### Theorems

```lean
greenMatrix_apply
greenMatrix_transpose
greenMatrix_of_transpose
greenMatrix_eq_zero_iff
greenForm_eq_greenMatrix
greenForm_eq_zero_of_symmetric
greenMatrix_add
greenForm_transpose
```

The main identity is

```math
\langle Hu,v\rangle-\langle u,Hv\rangle
=
\langle v,(H-H^\mathsf{T})u\rangle.
```

It is bilinear rather than sesquilinear. A later release can add the complex
adjoint convention without changing this finite transpose result.

## 4. Boundary compression

### Definitions

```lean
boundaryCorrection
boundaryOperator
```

For a boundary observation map `B`,

```math
\operatorname{boundaryCorrection}(B,\Delta)
=
B^\mathsf{T}\Delta B.
```

### Theorems

```lean
boundaryCorrection_transpose
greenMatrix_boundaryCorrection
greenMatrix_boundaryOperator
greenMatrix_boundaryOperator_of_symmetric_bulk
boundaryCorrection_symmetric
boundaryOperator_symmetric
boundaryCorrection_row_eq_zero
boundaryCorrection_column_eq_zero
boundaryCorrection_green_invariant
```

The central compression identity is

```math
\operatorname{Green}(B^\mathsf{T}\Delta B)
=
B^\mathsf{T}\operatorname{Green}(\Delta)B.
```

Consequently, a symmetric bulk plus a boundary correction has no Green defect
outside the vertices observed by `B`.

## 5. Deferred layers

The following belong to later, separately gated releases:

- canonical Hodge representative and its Pythagorean minimality;
- spanning-tree cut gauge and one seam per independent cycle;
- explicit rank bounds in terms of the cycle atlas;
- determinant and resolvent reduction to a boundary pencil;
- complex adjoint Green identities;
- analytical hypotheses for infinite-volume or localization claims.
