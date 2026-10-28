import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineOpenFormsUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CechBicomplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TermwiseIso
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains

/-! # Affine Cech Coordinate Unit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineCechCoordinateUnit.IntrinsicAffineCechCoordinateUnit

noncomputable section

/-! On an affine cover, the actual coordinate-form Čech bicomplex is identified by the native sheafification unit with the sheaf Čech calculation. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι : Type} (U : ι → X.left.Opens)

local instance : (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).Additive
  infer_instance

def bicomplex : HomologicalComplex₂ (ModuleCat.{0} R) (.up ℕ) (.up ℕ) :=
  ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

def map : bicomplex R X U ⟶
    IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.bicomplex R X U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) :=
  ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).mapHomologicalComplex (.up ℕ)).map
    (SheafificationComplex.SheafificationComplexUnit.unit (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X))

theorem row_isIso (hU : ∀ i, IsAffineOpen (U i)) (q : ℕ) : IsIso ((IntrinsicAffineCechCoordinateUnit.map R X U).f q) := by
  have : X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from X.hom]
    infer_instance
  apply Cech.TermwiseIso.CechTermwiseIso.isIso (FormalCoproduct.mk ι U).cech
    (toSheafify (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q))
  intro p t
  exact AffineOpenFormsUnit.IntrinsicAffineOpenFormsUnit.on_open R X (∏ᶜ (U ∘ t))
    (AlgebraicGeometry.SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU p t) q

theorem isIso (hU : ∀ i, IsAffineOpen (U i)) : IsIso (IntrinsicAffineCechCoordinateUnit.map R X U) := by
  have (q : ℕ) : IsIso ((IntrinsicAffineCechCoordinateUnit.map R X U).f q) := row_isIso R X U hU q
  exact HomologicalComplex.Hom.isIso_of_components _

def iso (hU : ∀ i, IsAffineOpen (U i)) : bicomplex R X U ≅
    IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.bicomplex R X U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) := by
  have : IsIso (IntrinsicAffineCechCoordinateUnit.map R X U) := isIso R X U hU
  exact asIso (IntrinsicAffineCechCoordinateUnit.map R X U)

def integerTotal : CochainComplex (ModuleCat.{0} R) ℤ :=
  ((bicomplex R X U).total (.up ℕ)).extend ComplexShape.embeddingUpNat

def totalIso (hU : ∀ i, IsAffineOpen (U i)) :
    integerTotal R X U ≅ IntrinsicCech.Terms.IntrinsicCechComparison.sections R X.left U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{0} R)).mapIso
    (HomologicalComplex₂.total.mapIso (iso R X U hU) (.up ℕ)) ≪≫
      IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.iso R X U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineCechCoordinateUnit.IntrinsicAffineCechCoordinateUnit
