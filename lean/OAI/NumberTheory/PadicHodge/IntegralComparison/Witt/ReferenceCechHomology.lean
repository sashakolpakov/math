import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CechTotalMapFactorization
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined

/-! # Reference Cech Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.ReferenceCechHomology.Reference

noncomputable section

/-! The native total-map factorization in the original abelian homology
coordinates, before choosing the coefficient complexes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

section
variable {D : Type*} [Category D] [Abelian D]
def originalMap {K L : CochainComplex D ℕ} (a : K ⟶ L) (q : ℕ) :=
  homologyMap a q
end

universe s t
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)
  {K L : CochainComplex (Cᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ}
  (a : K ⟶ L)

def map :
    AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U K ⟶
    AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U L :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (NonemptyCechNerve.nerve U) a

omit [Fintype k] [CharP k p] in
theorem homology (q : ℕ) :
    homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (NonemptyCechNerve.nerve U) a) q =
    originalMap (map p k U a) q := rfl

omit [Fintype k] [CharP k p] in
theorem comparison (q : ℕ)
    {T : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
    (b : (CechTotalMapFactorization.total p k U L).homology q ⟶ T)
    {f : (CechTotalMapFactorization.total p k U K).homology q ⟶ T}
    (h : f = homologyMap (CechTotalMapFactorization.map p k U a) q ≫ b) :
    f = originalMap (map p k U a) q ≫ b :=
  (CechTotalMapFactorization.comparison p k U a q b h).trans
    (congrArg (fun m => m ≫ b) (Reference.homology p k U a q))

omit [Fintype k] [CharP k p] in
theorem coefficient_comparison (q : ℕ)
    {T S : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
    (b : (CechTotalMapFactorization.total p k U L).homology q ⟶ T)
    {f : (CechTotalMapFactorization.total p k U K).homology q ⟶ T}
    (h : f = homologyMap (CechTotalMapFactorization.map p k U a) q ≫ b)
    (c c' : S ⟶ (CechTotalMapFactorization.total p k U K).homology q)
    (hc : c = c') :
    c ≫ f = c' ≫ originalMap (map p k U a) q ≫ b := by
  rw [hc, comparison p k U a q b h]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.ReferenceCechHomology.Reference
