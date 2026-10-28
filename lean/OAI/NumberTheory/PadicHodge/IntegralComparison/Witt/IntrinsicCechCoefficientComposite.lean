import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoefficientComposite

/-! # Intrinsic Cech Coefficient Composite -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.IntrinsicCechCoefficientComposite.Intrinsic

noncomputable section

/-! A coefficient and Čech homology composite with the native Witt
module categories fixed before choosing complexes or a resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

universe s t
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)
  (F : ModuleCat.{0} (WittVector p k) ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
  [F.Additive] [F.PreservesHomology]
  (Q : CochainComplex (ModuleCat.{0} (WittVector p k)) ℕ)
  {K L : CochainComplex (Cᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ}
  (e : (F.mapHomologicalComplex (.up ℕ)).obj Q ≅
    AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U K)

def coefficientIso (q : ℕ) :=
  @GeometricComparison.ExactHomology.ExactHomologyComparison.iso
    (@ModuleCat.{0} (WittVector p k) (WittVector.instCommRing p k).toRing)
    (@ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) ULift.ring)
    (@ModuleCat.moduleCategory (WittVector p k) (WittVector.instCommRing p k).toRing)
    (@ModuleCat.moduleCategory (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) ULift.ring)
    (@ModuleCat.abelian (WittVector p k) (WittVector.instCommRing p k).toRing)
    (@ModuleCat.abelian (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) ULift.ring)
    F _ _ ℕ (.up ℕ) Q
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U K) e q

def composite (a : K ⟶ L) (q : ℕ)
    {T : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
    (b : (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U L).homology q ⟶ T) :=
  (coefficientIso p k U F Q e q).hom ≫
    @ReferenceCechHomology.Reference.originalMap
      (@ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) ULift.ring)
      (@ModuleCat.moduleCategory (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) ULift.ring)
      (@ModuleCat.abelian (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) ULift.ring)
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{1,2}
        (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U K)
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{1,2}
        (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U L)
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2}
        (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
        (NonemptyCechNerve.nerve U) a) q ≫ b

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.IntrinsicCechCoefficientComposite.Intrinsic
