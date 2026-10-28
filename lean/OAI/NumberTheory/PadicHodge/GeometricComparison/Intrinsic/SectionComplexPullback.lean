import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.SectionCochainAdjoint
import OAI.NumberTheory.PadicHodge.GeometricComparison.LinearExact
import OAI.NumberTheory.PadicHodge.GeometricComparison.LinearCoefficient

/-! # Section Complex Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.SectionComplexPullback.IntrinsicSectionComplexPullback

noncomputable section

/-! The actual section-complex pullback is the coefficient-Hom pullback under the native section identifications. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).Additive where
  map_add := rfl
local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of Y.left)).Additive where
  map_add := rfl

variable {K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℤ}
  {L : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℤ}
  (a : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℤ)).obj K ⟶ L)

def map : Section.Hypercohomology.SectionHypercohomology.sectionComplex R (TopCat.of Y.left) K ⟶
    Section.Hypercohomology.SectionHypercohomology.sectionComplex R (TopCat.of X.left) L :=
  (NatTrans.mapHomologicalComplex (SectionCochainAdjoint.IntrinsicSectionPullback.map f) (.up ℤ)).app K ≫
    ((Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).mapHomologicalComplex (.up ℤ)).map a

def homMap : AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y) K ⟶
    AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) L :=
  LinearExact.LinearExactFunctorNaturality.complexMap R (DeRham.Int.inverseImage f) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y) a ≫
    LinearCoefficient.LinearCoefficientNaturality.complexMap R (DeRham.Int.inverseImageConstantIso f).inv L

theorem square : homMap f a ≫ (Section.Hypercohomology.SectionHypercohomology.homSectionsIso R (TopCat.of X.left) L).hom =
    (Section.Hypercohomology.SectionHypercohomology.homSectionsIso R (TopCat.of Y.left) K).hom ≫ IntrinsicSectionComplexPullback.map f a := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y ⟶ K.X n at z
  exact (congrArg (ConstantSheaf.ConstantSheafSections.linearEquiv R (TopCat.of X.left) (L.X n))
    (Category.assoc (DeRham.Int.inverseImageConstantIso f).inv ((DeRham.Int.inverseImage f).map z) (a.f n)).symm).trans
    ((ConstantSheaf.ConstantSheafSections.naturality R (TopCat.of X.left)
      ((DeRham.Int.inverseImageConstantIso f).inv ≫ (DeRham.Int.inverseImage f).map z) (a.f n)).trans
      (congrArg ((a.f n).hom.app (op ⊤)) (SectionCochainAdjoint.IntrinsicSectionPullback.coefficient_sections f (K.X n) z)))

theorem homologyEquiv (n : ℤ) (x : (Section.Hypercohomology.SectionHypercohomology.sectionComplex R (TopCat.of Y.left) K).homology n) :
    Section.Hypercohomology.SectionHypercohomology.homologyEquiv R (TopCat.of X.left) L n
      (HomologicalComplex.homologyMap (IntrinsicSectionComplexPullback.map f a) n x) =
      HomologicalComplex.homologyMap (homMap f a) n
        (Section.Hypercohomology.SectionHypercohomology.homologyEquiv R (TopCat.of Y.left) K n x) :=
  Section.Hypercohomology.SectionHypercohomology.map_inverse_square_apply (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) n)
    (Section.Hypercohomology.SectionHypercohomology.homSectionsIso R (TopCat.of Y.left) K)
    (Section.Hypercohomology.SectionHypercohomology.homSectionsIso R (TopCat.of X.left) L) _ _ (square f a) x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.SectionComplexPullback.IntrinsicSectionComplexPullback
