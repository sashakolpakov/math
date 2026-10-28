import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.GlobalCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.CechSheafification

/-! # Gamma Augmentation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.GammaAugmentation

noncomputable section

/-! The actual singular sheafification map agrees with the native global Cech augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0})

def rationalSingularToGamma :
    ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.mapHomologicalComplex (.up ℕ)).obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X)) ⟶
      FlasqueCechD.abelianDerivedSectionsComplex (Rational.BettiSheafComparison.rationalAbelianSingularResolution X) :=
  (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.mapHomologicalComplex (.up ℕ)).map
      (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X) ≫
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetSectionsComplexIso ⊤ (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).inv ≫
      (GammaSectionsComparison.abelianGammaSectionsIso (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).inv

theorem rationalSingularToGamma_top (q : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q) :
    (GammaSectionsComparison.abelianGammaSectionsIso (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).hom.f q
        ((rationalSingularToGamma X).f q c) =
      (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X).f q c := by
  let e := (HomologicalComplex.eval AddCommGrpCat.{0} (.up ℕ) q).mapIso
    (GammaSectionsComparison.abelianGammaSectionsIso (Rational.BettiSheafComparison.rationalAbelianSingularResolution X))
  change e.hom (e.inv ((AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X).f q c)) = _
  exact e.inv_hom_id_apply _

variable {I : Type} (U : I → Opens X)

theorem rationalSingularToGamma_augmentation (q : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q) :
    Abelian.CechCoordinates.abelianCechCoordinates ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X q).obj U 0
        (FlasqueCechD.abelianCechHorizontalAugmentation U (Rational.BettiSheafComparison.rationalAbelianSingularResolution X) q
          ((rationalSingularToGamma X).f q c)) =
      CechSheafification.singularCechSheafify U q 0
        ((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f q c) := by
  funext a
  erw [FlasqueCechD.abelianCechHorizontalAugmentation, Cech.GlobalCoordinates.abelianCechGlobalAugmentation_coordinates]
  change ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X q).obj.map (homOfLE le_top).op
    ((GammaSectionsComparison.abelianGammaSectionsIso (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).hom.f q
      ((rationalSingularToGamma X).f q c)) = _
  rw [rationalSingularToGamma_top]
  let eta := CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X q)
  let topc := (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (Opens.inclusion' (⊤ : Opens X))).f q c
  have h := ConcreteCategory.congr_hom
    (eta.naturality (homOfLE (show AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a ≤ ⊤ from le_top)).op) topc
  change ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X q).obj.map (homOfLE le_top).op
      (eta.app (op ⊤) topc) =
    eta.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
      (((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f q c) a)
  rw [Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation_apply]
  change eta.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
      ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X q).map (homOfLE le_top).op topc) =
    ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X q).obj.map (homOfLE le_top).op
      (eta.app (op ⊤) topc) at h
  rw [AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularTopRestriction_restrict] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.GammaAugmentation
