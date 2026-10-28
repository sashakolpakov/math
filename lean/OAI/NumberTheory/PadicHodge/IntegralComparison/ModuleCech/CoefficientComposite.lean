import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.ReferenceCechHomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Coefficient Composite -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoefficientComposite

noncomputable section

/-! A complete coefficient and Čech homology comparison with the original
module-category and total-complex instances fixed before specialization. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

universe uR uS vR vS s t
section Original
variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)
  (F : ModuleCat.{vS} S ⥤ ModuleCat.{max uR vR} R)
  [F.Additive] [F.PreservesHomology]
  (Q : CochainComplex (ModuleCat.{vS} S) ℕ)
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max uR vR} R) ℕ}
  (e : (F.mapHomologicalComplex (.up ℕ)).obj Q ≅
    AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{uR,vR} R U K)

def coefficientIso (q : ℕ) := GeometricComparison.ExactHomology.ExactHomologyComparison.iso F (.up ℕ)
  Q (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{uR,vR} R U K) e q

def composite (a : K ⟶ L) (q : ℕ) {T : ModuleCat.{max uR vR} R}
    (b : (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{uR,vR} R U L).homology q ⟶ T) :=
  (coefficientIso R S U F Q e q).hom ≫
    Witt.ReferenceCechHomology.Reference.originalMap
      (K := AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{uR,vR} R U K)
      (L := AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{uR,vR} R U L)
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R (NonemptyCechNerve.nerve U) a) q ≫ b
end Original

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)
  (F : ModuleCat (WittVector p k) ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
  [F.Additive] [F.PreservesHomology]
  (Q : CochainComplex (ModuleCat (WittVector p k)) ℕ)
  {K L : CochainComplex (Cᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ}
  (e : (F.mapHomologicalComplex (.up ℕ)).obj Q ≅
    AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U K)
  (a : K ⟶ L)

omit [Fintype k] [CharP k p] in
theorem comparison (q : ℕ)
    {T : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
    (b : (Witt.CechTotalMapFactorization.total p k U L).homology q ⟶ T)
    {f : (Witt.CechTotalMapFactorization.total p k U K).homology q ⟶ T}
    (h : f = homologyMap (Witt.CechTotalMapFactorization.map p k U a) q ≫ b)
    (c : F.obj (Q.homology q) ⟶ (Witt.CechTotalMapFactorization.total p k U K).homology q)
    (hc : c = (coefficientIso
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (WittVector p k)
      U F Q e q).hom) :
    c ≫ f = composite
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (WittVector p k)
      U F Q e a q b :=
  Witt.ReferenceCechHomology.Reference.coefficient_comparison p k U a q b h c
    (coefficientIso (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (WittVector p k) U F Q e q).hom hc

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoefficientComposite
