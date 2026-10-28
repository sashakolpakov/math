import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalAffineApproximation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.AffineNeighborhood
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalCurveCharts
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective

/-! # Approximation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Approximation

noncomputable section

/-! Finite order approximation on normal integral projective schemes of
arbitrary dimension, using the actual scheme function field and local orders. -/

set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe v

theorem exists_orders {X : Scheme} [IsIntegral X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type v} [Fintype ι] (x : ι → X)
    (hx : ∀ i, Order.coheight (x i) = 1) (hinj : Function.Injective x) (e : ι → ℤ) :
    letI : AlgebraicGeometry.IsNoetherian X := P.isNoetherian
    ∃ g : X.functionField, g ≠ 0 ∧ ∀ i, X.ord g (x i) = e i := by
  let : AlgebraicGeometry.IsNoetherian X := P.isNoetherian
  let : LocallyOfFiniteType f := P.finiteType.1
  obtain ⟨U, hU, hmem⟩ := AffineNeighborhood.common_affine P
    (fun i : Option ι => i.elim (genericPoint X) x)
  let : Nonempty U := ⟨⟨genericPoint X, hmem none⟩⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing ℂ Γ(X, U)
  let : IsIntegrallyClosed Γ(X, U) := NormalCurveCharts.sections_integrallyClosed hNormal U hU
  let q : ι → Spec Γ(X, U) := fun i => hU.primeIdealOf ⟨x i, hmem (some i)⟩
  have hq (i : ι) : hU.fromSpec (q i) = x i := hU.fromSpec_primeIdealOf _
  have hc (i : ι) : Order.coheight (q i) = 1 := by
    rw [← coheight_eq_of_isOpenImmersion hU.fromSpec, hq, hx]
  have hqinj : Function.Injective q := by
    intro i j h
    apply hinj
    rw [← hq i, ← hq j, h]
  obtain ⟨g, hg, he⟩ := NormalAffineApproximation.exists_orders Γ(X, U) q hc hqinj e
  let a := (Divisor.DivisorRestriction.openFieldIso hU.fromSpec).inv g
  have hag : Divisor.DivisorRestriction.openFieldMap hU.fromSpec a = g :=
    ConcreteCategory.congr_hom (Divisor.DivisorRestriction.openFieldIso hU.fromSpec).inv_hom_id g
  refine ⟨a, ?_, fun i => ?_⟩
  · intro ha
    apply hg
    rw [← hag, ha, map_zero]
  · rw [← hq i, ← Divisor.DivisorRestriction.ord_openImmersion hU.fromSpec, hag, he]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Approximation
