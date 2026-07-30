import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# Diagonal gauge covariance

This file isolates the algebraic gauge action used by finite Hatano--Nelson
operators.  A nowhere-zero vertex dressing acts on a matrix entry by

`H i j ↦ (d i)⁻¹ * H i j * d j`.

The statements are purely finite-dimensional and do not assume a graph,
spectrum, or continuum limit.
-/

namespace HatanoNelsonBoundaryAtlas

noncomputable section

variable {V K : Type*} [Fintype V] [DecidableEq V] [Field K]

/-- Diagonal similarity written entrywise. -/
def diagonalGauge (d : V → K) (H : Matrix V V K) : Matrix V V K :=
  fun i j => (d i)⁻¹ * H i j * d j

@[simp] theorem diagonalGauge_apply
    (d : V → K) (H : Matrix V V K) (i j : V) :
    diagonalGauge d H i j = (d i)⁻¹ * H i j * d j :=
  rfl

/-- The unit vertex dressing acts trivially. -/
@[simp] theorem diagonalGauge_one (H : Matrix V V K) :
    diagonalGauge (fun _ => 1) H = H := by
  ext i j
  simp [diagonalGauge]

/-- Successive vertex dressings multiply pointwise. -/
theorem diagonalGauge_comp
    (d e : V → K) (H : Matrix V V K) :
    diagonalGauge e (diagonalGauge d H) =
      diagonalGauge (fun i => d i * e i) H := by
  ext i j
  simp only [diagonalGauge]
  rw [mul_inv_rev]
  ring

/-- Entrywise gauge covariance is ordinary diagonal matrix similarity. -/
theorem diagonalGauge_eq_diagonal_mul
    (d : V → K) (H : Matrix V V K) :
    diagonalGauge d H =
      Matrix.diagonal (fun i => (d i)⁻¹) * H * Matrix.diagonal d := by
  ext i j
  simp [diagonalGauge]

/-- A nowhere-zero gauge leaves every diagonal entry unchanged. -/
theorem diagonalGauge_diagonal
    (d : V → K) (H : Matrix V V K)
    (hd : ∀ i, d i ≠ 0) (i : V) :
    diagonalGauge d H i i = H i i := by
  field_simp [diagonalGauge, hd i]

/-- A nowhere-zero diagonal similarity preserves the zero pattern exactly. -/
theorem diagonalGauge_eq_zero_iff
    (d : V → K) (H : Matrix V V K)
    (hd : ∀ i, d i ≠ 0) (i j : V) :
    diagonalGauge d H i j = 0 ↔ H i j = 0 := by
  simp [diagonalGauge, hd i, hd j]

/-- Multiplicative carrier attached to each ordered pair of vertices. -/
abbrev EdgeCarrier (V K : Type*) := V → V → K

/-- Vertex dressing of a multiplicative edge carrier. -/
def carrierGauge
    (d : V → K) (r : EdgeCarrier V K) : EdgeCarrier V K :=
  fun i j => (d i)⁻¹ * r i j * d j

@[simp] theorem carrierGauge_apply
    (d : V → K) (r : EdgeCarrier V K) (i j : V) :
    carrierGauge d r i j = (d i)⁻¹ * r i j * d j :=
  rfl

/-- A carrier-dressed hopping matrix. -/
def carrierMatrix
    (J : Matrix V V K) (r : EdgeCarrier V K) : Matrix V V K :=
  fun i j => J i j * r i j

@[simp] theorem carrierMatrix_apply
    (J : Matrix V V K) (r : EdgeCarrier V K) (i j : V) :
    carrierMatrix J r i j = J i j * r i j :=
  rfl

/-- Dressing the edge carrier is exactly diagonal similarity of the hopping
matrix. -/
theorem carrierMatrix_carrierGauge
    (d : V → K) (J : Matrix V V K) (r : EdgeCarrier V K) :
    carrierMatrix J (carrierGauge d r) =
      diagonalGauge d (carrierMatrix J r) := by
  ext i j
  simp only [carrierMatrix, carrierGauge, diagonalGauge]
  ring

/-- Nowhere-zero vertex dressing also preserves the carrier zero pattern. -/
theorem carrierGauge_eq_zero_iff
    (d : V → K) (r : EdgeCarrier V K)
    (hd : ∀ i, d i ≠ 0) (i j : V) :
    carrierGauge d r i j = 0 ↔ r i j = 0 := by
  simp [carrierGauge, hd i, hd j]

end

end HatanoNelsonBoundaryAtlas
