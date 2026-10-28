import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Approximation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.DivisorComparison

/-! # Approximation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Approximation

noncomputable section

/-! Arbitrary orders can be prescribed at finitely many divisor
points of the actual finite normalization of a projective scheme.
The affine chart comes from the original projective presentation. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.DivisorComparison

theorem exists_orders {X : Scheme} [IsIntegral X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) {ι : Type} [Fintype ι]
    (y : ι → Normalization.Scheme.normalization X) (hy : ∀ i, Order.coheight (y i) = 1)
    (hinj : Function.Injective y) (e : ι → ℤ) :
    letI : AlgebraicGeometry.IsNoetherian X := P.isNoetherian
    letI : LocallyOfFiniteType f := P.finiteType.1
    letI := DivisorComparison.normalization_noetherian X f
    ∃ g : (Normalization.Scheme.normalization X).functionField, g ≠ 0 ∧ ∀ i, (Normalization.Scheme.normalization X).ord g (y i) = e i := by
  let : AlgebraicGeometry.IsNoetherian X := P.isNoetherian
  let : LocallyOfFiniteType f := P.finiteType.1
  let := DivisorComparison.normalization_noetherian X f
  obtain ⟨U, hU, hmem⟩ := Projective.AffineNeighborhood.common_affine P
    (fun i : Option ι => i.elim (genericPoint X) (fun i => Normalization.Scheme.normalizationMap X (y i)))
  let : Nonempty U := ⟨⟨genericPoint X, hmem none⟩⟩
  let V := Normalization.Scheme.normalizationMap X ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage (Normalization.Scheme.normalizationMap X)
  have hgV : genericPoint (Normalization.Scheme.normalization X) ∈ V := by
    change Normalization.Scheme.normalizationMap X (genericPoint (Normalization.Scheme.normalization X)) ∈ U
    rw [Fields.normalizationMap_genericPoint]
    exact hmem none
  let : Nonempty V := ⟨⟨genericPoint (Normalization.Scheme.normalization X), hgV⟩⟩
  let : IsIntegrallyClosed Γ(Normalization.Scheme.normalization X, V) := Normalization.Scheme.normalization_affineSections_integrallyClosed X U hU
  let : IsNoetherianRing Γ(Normalization.Scheme.normalization X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let q : ι → Spec Γ(Normalization.Scheme.normalization X, V) := fun i => hV.primeIdealOf ⟨y i, hmem (some i)⟩
  have hq (i : ι) : hV.fromSpec (q i) = y i := hV.fromSpec_primeIdealOf _
  have hheight (i : ι) : Order.coheight (q i) = 1 := by
    rw [← coheight_eq_of_isOpenImmersion hV.fromSpec, hq, hy]
  have hqinj : Function.Injective q := by
    intro i j he
    apply hinj
    rw [← hq i, ← hq j, he]
  obtain ⟨g, hg, he⟩ := NormalAffineApproximation.exists_orders Γ(Normalization.Scheme.normalization X, V) q hheight hqinj e
  let a := (Divisor.DivisorRestriction.openFieldIso hV.fromSpec).inv g
  have hag : Divisor.DivisorRestriction.openFieldMap hV.fromSpec a = g :=
    ConcreteCategory.congr_hom (Divisor.DivisorRestriction.openFieldIso hV.fromSpec).inv_hom_id g
  refine ⟨a, ?_, fun i => ?_⟩
  · intro ha
    apply hg
    rw [← hag, ha, map_zero]
  · rw [← hq i, ← Divisor.DivisorRestriction.ord_openImmersion hV.fromSpec, hag, he]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Approximation
