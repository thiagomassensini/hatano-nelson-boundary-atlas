import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# Finite discrete Green form

For the symmetric bilinear pairing, the difference between the two operator
placements is controlled exactly by `H - Hᵀ`.  This is the finite matrix
version of the discrete Green identity.
-/

namespace HatanoNelsonBoundaryAtlas

noncomputable section

open Matrix

variable {V K : Type*} [Fintype V] [CommRing K]

/-- Matrix carrying the bilinear Green defect. -/
def greenMatrix (H : Matrix V V K) : Matrix V V K :=
  H - H.transpose

@[simp] theorem greenMatrix_apply
    (H : Matrix V V K) (i j : V) :
    greenMatrix H i j = H i j - H j i :=
  rfl

/-- The Green matrix is skew under transpose. -/
theorem greenMatrix_transpose (H : Matrix V V K) :
    (greenMatrix H).transpose = -greenMatrix H := by
  ext i j
  simp [greenMatrix]
  ring

/-- The Green matrix vanishes exactly for a symmetric matrix. -/
theorem greenMatrix_eq_zero_iff (H : Matrix V V K) :
    greenMatrix H = 0 ↔ H.transpose = H := by
  simp [greenMatrix, eq_comm]

/-- Green defect for the symmetric bilinear pairing. -/
def greenForm
    (H : Matrix V V K) (u v : V → K) : K :=
  (H *ᵥ u) ⬝ᵥ v - u ⬝ᵥ (H *ᵥ v)

/-- Exact finite Green identity: the action difference is the bilinear form of
`H - Hᵀ`. -/
theorem greenForm_eq_greenMatrix
    (H : Matrix V V K) (u v : V → K) :
    greenForm H u v =
      v ⬝ᵥ (greenMatrix H *ᵥ u) := by
  calc
    greenForm H u v =
        v ⬝ᵥ (H *ᵥ u) - v ⬝ᵥ (H.transpose *ᵥ u) := by
      rw [greenForm, dotProduct_comm (H *ᵥ u) v,
        dotProduct_transpose_mulVec]
    _ = v ⬝ᵥ ((H - H.transpose) *ᵥ u) := by
      rw [sub_mulVec, dotProduct_sub]
    _ = v ⬝ᵥ (greenMatrix H *ᵥ u) := by
      rfl

/-- Symmetric operators have zero Green defect. -/
theorem greenForm_eq_zero_of_symmetric
    (H : Matrix V V K) (hH : H.transpose = H)
    (u v : V → K) :
    greenForm H u v = 0 := by
  rw [greenForm_eq_greenMatrix]
  simp [greenMatrix, hH]

/-- The Green matrix is additive. -/
theorem greenMatrix_add
    (H G : Matrix V V K) :
    greenMatrix (H + G) = greenMatrix H + greenMatrix G := by
  ext i j
  simp [greenMatrix]
  ring

/-- Transposition reverses the Green defect. -/
theorem greenForm_transpose
    (H : Matrix V V K) (u v : V → K) :
    greenForm H.transpose u v = -greenForm H u v := by
  rw [greenForm_eq_greenMatrix, greenForm_eq_greenMatrix]
  simp [greenMatrix, sub_eq_add_neg, add_comm]

end

end HatanoNelsonBoundaryAtlas
