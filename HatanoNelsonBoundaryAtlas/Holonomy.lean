import HatanoNelsonBoundaryAtlas.Gauge

/-!
# Closed-walk holonomy

The product of multiplicative carriers around a closed walk is invariant under
every nowhere-zero vertex dressing.  This is the finite algebraic obstruction
that survives diagonal gauge removal.
-/

namespace HatanoNelsonBoundaryAtlas

noncomputable section

variable {V K : Type*} [Field K]

/-- Product of carriers along consecutive vertices of a path. -/
def pathCarrier (r : EdgeCarrier V K) : List V → K
  | [] => 1
  | [_] => 1
  | u :: v :: rest => r u v * pathCarrier r (v :: rest)

/-- Last vertex of a path represented by its first vertex and remaining list. -/
def lastVertex (start : V) : List V → V
  | [] => start
  | v :: rest => lastVertex v rest

/-- Closing the path back to its first vertex produces its cycle carrier. -/
def cycleCarrier
    (r : EdgeCarrier V K) (start : V) (rest : List V) : K :=
  pathCarrier r (start :: rest) * r (lastVertex start rest) start

/-- Endpoint covariance of an open carrier product. -/
theorem pathCarrier_carrierGauge
    (d : V → K) (hd : ∀ i, d i ≠ 0)
    (r : EdgeCarrier V K) (start : V) (rest : List V) :
    pathCarrier (carrierGauge d r) (start :: rest) =
      (d start)⁻¹ * pathCarrier r (start :: rest) *
        d (lastVertex start rest) := by
  induction rest generalizing start with
  | nil =>
      simp [pathCarrier, lastVertex, hd start]
  | cons v tail ih =>
      simp only [pathCarrier, lastVertex]
      rw [ih v]
      simp only [carrierGauge]
      field_simp [hd start, hd v] <;> ring

/-- Closed-walk holonomy is invariant under vertex dressing. -/
theorem cycleCarrier_carrierGauge
    (d : V → K) (hd : ∀ i, d i ≠ 0)
    (r : EdgeCarrier V K) (start : V) (rest : List V) :
    cycleCarrier (carrierGauge d r) start rest =
      cycleCarrier r start rest := by
  unfold cycleCarrier
  rw [pathCarrier_carrierGauge d hd r start rest]
  simp only [carrierGauge]
  field_simp [hd start, hd (lastVertex start rest)] <;> ring

/-- The constant unit carrier has unit product along every path. -/
@[simp] theorem pathCarrier_one (vertices : List V) :
    pathCarrier (fun _ _ => (1 : K)) vertices = 1 := by
  induction vertices with
  | nil => rfl
  | cons u tail ih =>
      cases tail with
      | nil => rfl
      | cons v rest =>
          simpa [pathCarrier] using ih

/-- The constant unit carrier has unit holonomy on every closed walk. -/
@[simp] theorem cycleCarrier_one (start : V) (rest : List V) :
    cycleCarrier (fun _ _ => (1 : K)) start rest = 1 := by
  simp [cycleCarrier]

/-- A pure vertex gauge has trivial holonomy around every closed walk. -/
theorem pureGauge_cycleCarrier
    (d : V → K) (hd : ∀ i, d i ≠ 0)
    (start : V) (rest : List V) :
    cycleCarrier (carrierGauge d (fun _ _ => (1 : K))) start rest = 1 := by
  rw [cycleCarrier_carrierGauge d hd]
  simp

end

end HatanoNelsonBoundaryAtlas
