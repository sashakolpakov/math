import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveGeneration
import Mathlib.Topology.Algebra.Group.Basic

/-! # Active Product Density -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveProductDensity.Approximation

noncomputable section

/-! Approximation of the four active root groups, with away coordinate
one, gives density in the product with the actual range of the away map. -/

open scoped Classical _root_.Matrix
open _root_.Matrix.SpecialLinearGroup

variable {K : Type*} [Field K] [TopologicalSpace (Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL K)] [IsTopologicalGroup (Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL K)]
  {A G : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group G]

theorem denseRange_product_of_active_roots (r : G →* Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL K × A)
    (haway : Function.Surjective (fun g => (r g).2))
    (hforward : ∀ (i : Fin 3) (hi : i ≠ 2) (a : K),
      (transvection hi a, (1 : A)) ∈ r.range.topologicalClosure)
    (hbackward : ∀ (i : Fin 3) (hi : i ≠ 2) (a : K),
      (transvection hi.symm a, (1 : A)) ∈ r.range.topologicalClosure) : DenseRange r := by
  let H := r.range.topologicalClosure
  let J := H.comap (MonoidHom.inl (Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL K) A)
  have hJ : J = ⊤ := ActiveGeneration.Approximation.subgroup_eq_top_of_active_roots J hforward hbackward
  have hactive (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL K) : (g, (1 : A)) ∈ H := by
    change g ∈ J
    rw [hJ]
    trivial
  intro x
  change x ∈ H
  obtain ⟨γ, hγ⟩ := haway x.2
  have hr : r γ ∈ H := r.range.le_topologicalClosure ⟨γ, rfl⟩
  have hp := H.mul_mem (hactive (x.1 * (r γ).1⁻¹)) hr
  have he : (x.1 * (r γ).1⁻¹, (1 : A)) * r γ = x := by
    apply Prod.ext
    · simp [mul_assoc]
    · simpa using hγ
  exact he ▸ hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveProductDensity.Approximation
