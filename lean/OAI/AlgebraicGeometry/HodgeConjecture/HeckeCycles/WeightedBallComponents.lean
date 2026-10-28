import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource
import OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

/-! # Weighted Ball Components -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeightedBallComponents.CM

noncomputable section

/-! Explicit diagonal coordinates carry a weighted ball line and its
Hermitian annihilator to the ordinary line and dual annihilator. -/

open scoped Classical
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

variable (r s : ℂ) (hr : r ≠ 0) (hs : s ≠ 0)

def standard : GeometricSource.CM.Vec ℂ →ₗ[ℂ] GeometricSource.CM.Vec ℂ where
  toFun x i := (if i = 2 then r else 1) * s * x i
  map_add' x y := by funext i; exact mul_add _ _ _
  map_smul' c x := by funext i; change _ * (c * x i) = c * (_ * x i); ring

def dual (x : GeometricSource.CM.Vec ℂ) : GeometricSource.CM.Vec ℂ := fun i => (if i = 2 then r else -1) * s * x i

include hr hs in
theorem standard_injective : Function.Injective (standard r s) := by
  intro x y h
  funext i
  have hi := congrFun h i
  change ((if i = 2 then r else 1) * s) * x i = ((if i = 2 then r else 1) * s) * y i at hi
  exact mul_left_cancel₀ (mul_ne_zero (by split_ifs; exact hr; exact one_ne_zero) hs) hi

include hr in
theorem standard_line (z : GeometricSource.CM.BallChart) :
    standard r s (GeometricSource.CM.BallDatum.lineVector z) = (r * s) • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (fun i => z i / r) := by
  funext i
  fin_cases i <;> simp [standard, GeometricSource.CM.BallDatum.lineVector, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector]
  all_goals field_simp

include hr hs in
theorem line_iff (z : GeometricSource.CM.BallChart) (x : GeometricSource.CM.Vec ℂ) :
    (∃ c : ℂ, ∀ i, standard r s x i = RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (fun j => z j / r) i * c) ↔
      x ∈ ℂ ∙ GeometricSource.CM.BallDatum.lineVector z := by
  constructor
  · rintro ⟨c, hc⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c / (r * s), ?_⟩
    apply standard_injective r s hr hs
    rw [map_smul, standard_line r s hr, smul_smul]
    rw [div_mul_cancel₀ c (mul_ne_zero hr hs)]
    funext i
    exact (mul_comm _ _).trans (hc i).symm
  · intro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨c * (r * s), ?_⟩
    intro i
    rw [map_smul, standard_line r s hr]
    change c * ((r * s) * _) = _
    ring

include hr in
theorem dual_pairing (z : GeometricSource.CM.BallChart) (x : GeometricSource.CM.Vec ℂ) :
    dotProduct (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (fun i => z i / r)) (dual r s x) =
      -(s / r) * (z 0 * x 0 + z 1 * x 1 - r ^ 2 * x 2) := by
  simp [dotProduct, Fin.sum_univ_succ, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector, dual]
  field_simp
  ring

include hr hs in
theorem annihilator_iff (z : GeometricSource.CM.BallChart) (x : GeometricSource.CM.Vec ℂ) :
    dotProduct (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (fun i => z i / r)) (dual r s x) = 0 ↔
      z 0 * x 0 + z 1 * x 1 - r ^ 2 * x 2 = 0 := by
  rw [dual_pairing r s hr, mul_eq_zero]
  simp only [neg_ne_zero.mpr (div_ne_zero hs hr), false_or]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeightedBallComponents.CM
