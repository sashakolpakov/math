import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.ReferenceCechHomology

/-! # Reference Cech Composite -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.ReferenceCechComposite

noncomputable section

/-! Normalize a complete original Čech homology composite before
specializing its coefficient complexes and output. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

namespace Reference
universe u v s t
section Original
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ} (a : K ⟶ L) (q : ℕ)
  {S T : ModuleCat.{max u v} R}

def composite
    (c : S ⟶ (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total R U K).homology q)
    (b : (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total R U L).homology q ⟶ T) :=
  c ≫ ReferenceCechHomology.Reference.originalMap
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R (NonemptyCechNerve.nerve U) a) q ≫ b
end Original

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)
  {K L : CochainComplex (Cᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ}
  (a : K ⟶ L)

omit [Fintype k] [CharP k p] in
theorem comparison (q : ℕ)
    {T S : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
    (b : (CechTotalMapFactorization.total p k U L).homology q ⟶ T)
    {f : (CechTotalMapFactorization.total p k U K).homology q ⟶ T}
    (h : f = homologyMap (CechTotalMapFactorization.map p k U a) q ≫ b)
    (c c' : S ⟶ (CechTotalMapFactorization.total p k U K).homology q)
    (hc : c = c') :
    c ≫ f = composite.{1,2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      U a q c' b :=
  ReferenceCechHomology.Reference.coefficient_comparison p k U a q b h c c' hc

end Reference

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.ReferenceCechComposite
