import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveRotation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveProductDensity

/-! # Rotated Active Density -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RotatedActiveDensity.Approximation

noncomputable section

/-! One approximated binary subgroup and the rational positive rotation
give all four active roots while keeping the away coordinate equal to one. -/

open scoped Classical _root_.Matrix
open _root_.Matrix.SpecialLinearGroup

variable {K : Type*} [Field K] [TopologicalSpace (Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL K)] [IsTopologicalGroup (Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL K)]
  {A G : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group G]

theorem denseRange_product_of_binary_and_rotation (r : G →* Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL K × A)
    (haway : Function.Surjective (fun g => (r g).2))
    (γ : G) (hγ : (r γ).1 = ActiveRotation.Approximation.positiveRotation K)
    (hforward : ∀ a : K,
      (transvection (show (0 : Fin 3) ≠ 2 by decide) a, (1 : A)) ∈ r.range.topologicalClosure)
    (hbackward : ∀ a : K,
      (transvection (show (2 : Fin 3) ≠ 0 by decide) a, (1 : A)) ∈ r.range.topologicalClosure) :
    DenseRange r := by
  let H := r.range.topologicalClosure
  have hr : r γ ∈ H := r.range.le_topologicalClosure ⟨γ, rfl⟩
  have hc (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL K) (hg : (g, (1 : A)) ∈ H) :
      (ActiveRotation.Approximation.positiveRotation K * g * (ActiveRotation.Approximation.positiveRotation K)⁻¹, (1 : A)) ∈ H := by
    have hm := H.mul_mem (H.mul_mem hr hg) (H.inv_mem hr)
    convert hm using 1
    simp [Prod.ext_iff, hγ]
  apply ActiveProductDensity.Approximation.denseRange_product_of_active_roots r haway
  · intro i hi a
    fin_cases i
    · exact hforward a
    · simpa only [ActiveRotation.Approximation.positiveRotation_forward] using hc _ (hforward a)
    · exact (hi rfl).elim
  · intro i hi a
    fin_cases i
    · exact hbackward a
    · simpa only [ActiveRotation.Approximation.positiveRotation_backward] using hc _ (hbackward a)
    · exact (hi rfl).elim

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RotatedActiveDensity.Approximation
