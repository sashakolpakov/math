import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.ReferenceCechComposite

/-! # Intrinsic Cech Composite -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.IntrinsicCechComposite.Intrinsic

noncomputable section

/-! Native coefficient and abelian homology structures are fixed before
choosing the presheaf complexes of a Cech comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

universe u v s t
private def originalComposite {D : Type u} [Category.{v} D] [Abelian D]
    {K L : CochainComplex D ℕ} (a : K ⟶ L) (q : ℕ) {S T : D}
    (c : S ⟶ K.homology q) (b : L.homology q ⟶ T) : S ⟶ T :=
  c ≫ homologyMap a q ≫ b

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ}
  (a : K ⟶ L)

abbrev composite (q : ℕ) :=
  @originalComposite
    (@ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) ULift.ring)
    (@ModuleCat.moduleCategory (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) ULift.ring)
    (@ModuleCat.abelian (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) ULift.ring)
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U K)
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U L)
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (NonemptyCechNerve.nerve U) a) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.IntrinsicCechComposite.Intrinsic
