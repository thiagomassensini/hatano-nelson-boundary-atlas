import HatanoNelsonBoundaryAtlas.Green

/-!
# Exact boundary compression

An operator correction supported through a boundary map `B` has the form

`Bᵀ * Δ * B`.

Its entire Green defect is therefore the lift of the smaller boundary Green
matrix `Δ - Δᵀ`.  The bulk dimension does not enter this identity.
-/

namespace HatanoNelsonBoundaryAtlas

noncomputable section

open Matrix

variable {V B K : Type*}
  [Fintype B] [CommRing K]

/-- Lift a boundary matrix through a boundary observation map. -/
def boundaryCorrection
    (traceMap : Matrix B V K) (delta : Matrix B B K) :
    Matrix V V K :=
  traceMap.transpose * delta * traceMap

/-- Add a compressed boundary correction to a bulk operator. -/
def boundaryOperator
    (bulk : Matrix V V K)
    (traceMap : Matrix B V K) (delta : Matrix B B K) :
    Matrix V V K :=
  bulk + boundaryCorrection traceMap delta

/-- Transposition stays inside the same boundary atlas. -/
theorem boundaryCorrection_transpose
    (traceMap : Matrix B V K) (delta : Matrix B B K) :
    (boundaryCorrection traceMap delta).transpose =
      boundaryCorrection traceMap delta.transpose := by
  unfold boundaryCorrection
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  exact
    (mul_assoc traceMap.transpose delta.transpose traceMap).symm

/-- Exact compression of the boundary Green matrix. -/
theorem greenMatrix_boundaryCorrection
    (traceMap : Matrix B V K) (delta : Matrix B B K) :
    greenMatrix (boundaryCorrection traceMap delta) =
      boundaryCorrection traceMap (greenMatrix delta) := by
  unfold greenMatrix
  rw [boundaryCorrection_transpose]
  unfold boundaryCorrection
  noncomm_ring

/-- The full Green matrix splits into bulk and boundary contributions. -/
theorem greenMatrix_boundaryOperator
    (bulk : Matrix V V K)
    (traceMap : Matrix B V K) (delta : Matrix B B K) :
    greenMatrix (boundaryOperator bulk traceMap delta) =
      greenMatrix bulk +
        boundaryCorrection traceMap (greenMatrix delta) := by
  rw [boundaryOperator, greenMatrix_add,
    greenMatrix_boundaryCorrection]

/-- If the bulk is symmetric, every irreducible Green defect is carried by the
boundary atlas. -/
theorem greenMatrix_boundaryOperator_of_symmetric_bulk
    (bulk : Matrix V V K)
    (traceMap : Matrix B V K) (delta : Matrix B B K)
    (hbulk : bulk.transpose = bulk) :
    greenMatrix (boundaryOperator bulk traceMap delta) =
      boundaryCorrection traceMap (greenMatrix delta) := by
  rw [greenMatrix_boundaryOperator]
  simp [greenMatrix, hbulk]

/-- A symmetric boundary pencil produces a symmetric lifted correction. -/
theorem boundaryCorrection_symmetric
    (traceMap : Matrix B V K) (delta : Matrix B B K)
    (hdelta : delta.transpose = delta) :
    (boundaryCorrection traceMap delta).transpose =
      boundaryCorrection traceMap delta := by
  rw [boundaryCorrection_transpose, hdelta]

/-- Symmetric bulk and symmetric boundary data give a symmetric full
operator. -/
theorem boundaryOperator_symmetric
    (bulk : Matrix V V K)
    (traceMap : Matrix B V K) (delta : Matrix B B K)
    (hbulk : bulk.transpose = bulk)
    (hdelta : delta.transpose = delta) :
    (boundaryOperator bulk traceMap delta).transpose =
      boundaryOperator bulk traceMap delta := by
  simp [boundaryOperator, boundaryCorrection_transpose,
    hbulk, hdelta]

/-- If a bulk vertex is invisible to the boundary map, the lifted correction
has a zero row there. -/
theorem boundaryCorrection_row_eq_zero
    (traceMap : Matrix B V K) (delta : Matrix B B K)
    (i : V) (hi : ∀ b, traceMap b i = 0) :
    ∀ j, boundaryCorrection traceMap delta i j = 0 := by
  intro j
  simp [boundaryCorrection, Matrix.mul_apply, hi]

/-- If a bulk vertex is invisible to the boundary map, the lifted correction
has a zero column there. -/
theorem boundaryCorrection_column_eq_zero
    (traceMap : Matrix B V K) (delta : Matrix B B K)
    (j : V) (hj : ∀ b, traceMap b j = 0) :
    ∀ i, boundaryCorrection traceMap delta i j = 0 := by
  intro i
  simp [boundaryCorrection, Matrix.mul_apply, hj]

/-- Equality of boundary Green matrices is enough to identify the lifted
Green defects. -/
theorem boundaryCorrection_green_invariant
    (traceMap : Matrix B V K) (delta₁ delta₂ : Matrix B B K)
    (hgreen : greenMatrix delta₁ = greenMatrix delta₂) :
    greenMatrix (boundaryCorrection traceMap delta₁) =
      greenMatrix (boundaryCorrection traceMap delta₂) := by
  rw [greenMatrix_boundaryCorrection,
    greenMatrix_boundaryCorrection, hgreen]

end

end HatanoNelsonBoundaryAtlas
