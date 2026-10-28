import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeSheafUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CechBicomplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TermwiseIso
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains

/-! # Cech Coordinate Unit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit

noncomputable section

/-! Coordinate Čech cochains through form degree two agree with the actual native integral sheaf Čech complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι : Type} (U : ι → X.left.Opens)

local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)

local instance : (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).Additive
  infer_instance

def bicomplex : HomologicalComplex₂ (ModuleCat.{0} R) (.up ℕ) (.up ℕ) :=
  ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).mapHomologicalComplex (.up ℕ)).obj P

def map : bicomplex R X U ⟶ IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.bicomplex R X U K :=
  ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).mapHomologicalComplex (.up ℕ)).map
    (IntegralFirst.ThreeSheafUnit.IntegralFirstThreeSheafUnit.map R X)

theorem ordinary_row_isIso (hU : ∀ i, IsAffineOpen (U i)) (q : ℕ) (hq : q ≤ 2) :
    IsIso ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).map
      (toSheafify (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q))) := by
  have : X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from X.hom]
    infer_instance
  apply Cech.TermwiseIso.CechTermwiseIso.isIso (FormalCoproduct.mk ι U).cech
    (toSheafify (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q))
  intro p t
  exact OpenFormsUnit.IntegralAffineOpenFormsUnit.on_open R X (∏ᶜ (U ∘ t))
    (AlgebraicGeometry.SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU p t) q hq

theorem row_isIso (hU : ∀ i, IsAffineOpen (U i)) (q : ℕ) : IsIso ((IntegralAffineCechCoordinateUnit.map R X U).f q) := by
  rcases q with _ | (_ | (_ | q))
  · exact ordinary_row_isIso R X U hU 0 (by omega)
  · exact ordinary_row_isIso R X U hU 1 (by omega)
  · exact ordinary_row_isIso R X U hU 2 (by omega)
  · let : IsIso ((IntegralFirst.ThreeSheafUnit.IntegralFirstThreeSheafUnit.map R X).f (q + 3)) :=
      IntegralFirst.ThreeSheafUnit.IntegralFirstThreeSheafUnit.high_isIso R X q
    exact (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).map_isIso ((IntegralFirst.ThreeSheafUnit.IntegralFirstThreeSheafUnit.map R X).f (q + 3))

def iso (hU : ∀ i, IsAffineOpen (U i)) : bicomplex R X U ≅ IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.bicomplex R X U K := by
  have (q : ℕ) : IsIso ((IntegralAffineCechCoordinateUnit.map R X U).f q) := row_isIso R X U hU q
  have : IsIso (IntegralAffineCechCoordinateUnit.map R X U) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (IntegralAffineCechCoordinateUnit.map R X U)

def integerTotal : CochainComplex (ModuleCat.{0} R) ℤ :=
  ((bicomplex R X U).total (.up ℕ)).extend ComplexShape.embeddingUpNat

def totalIso (hU : ∀ i, IsAffineOpen (U i)) :
    integerTotal R X U ≅ IntrinsicCech.Terms.IntrinsicCechComparison.sections R X.left U K :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{0} R)).mapIso
    (HomologicalComplex₂.total.mapIso (iso R X U hU) (.up ℕ)) ≪≫
      IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.iso R X U K

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit
