import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.AnalytificationScalars
import OAI.AlgebraicGeometry.SheafCohomology.CechLinearComparison

/-! # Cech Analytification Linear -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CechAnalytificationLinear

noncomputable section

section

/-! The original algebraic Cech H1 embeds complex linearly in actual
native holomorphic H1, using the specified complex-base scalar actions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) {I : Type} (U : I → A.carrier.Opens) (hU : iSup U = ⊤)

local instance cechLinearNativeH1Group :
    AddCommGroup (CategoryTheory.Sheaf.H (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf A.variety.analyticModel A.variety.analyticSpace) 1) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of A.variety.analyticSpace)
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf A.variety.analyticModel A.variety.analyticSpace) 1

def cechAnalytificationH1Linear :
    letI := SheafCohomology.CechScalars.Projective.cechComplexCohomologyModule A (HilbertConstruction.Line.Bundles.structureModule A.carrier) U 1
    letI := Holomorphic.Scalars.nativeHolomorphicH1Module A.variety.analyticModel A.variety.analyticSpace
    (SheafCohomology.CechScalars.Projective.moduleCechCohomologyFunctor U 1).obj (HilbertConstruction.Line.Bundles.structureModule A.carrier) →ₗ[ℂ]
      CategoryTheory.Sheaf.H (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf A.variety.analyticModel A.variety.analyticSpace) 1 := by
  letI := SheafCohomology.CechScalars.Projective.cechComplexCohomologyModule A (HilbertConstruction.Line.Bundles.structureModule A.carrier) U 1
  letI := Holomorphic.Scalars.nativeHolomorphicH1Module A.variety.analyticModel A.variety.analyticSpace
  exact {
    toFun := Cech.Analytification.cechAnalytificationH1 A.variety U hU
    map_add' := (Cech.Analytification.cechAnalytificationH1 A.variety U hU).hom.map_add
    map_smul' c x := ConcreteCategory.congr_hom (Cech.AnalytificationScalars.cechAnalytificationH1_scalar A U hU c) x }

theorem cechAnalytificationH1Linear_injective :
    Function.Injective (cechAnalytificationH1Linear A U hU) :=
  Cech.Analytification.cechAnalytificationH1_injective A.variety U hU

end

/-! The original Zariski H1 of the structure sheaf embeds complex
linearly in actual native holomorphic H1 through an affine Cech cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

local instance structureNativeH1Group :
    AddCommGroup (CategoryTheory.Sheaf.H (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf A.variety.analyticModel A.variety.analyticSpace) 1) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of A.variety.analyticSpace)
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf A.variety.analyticModel A.variety.analyticSpace) 1

def structureH1Analytification :
    letI := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
    letI := Holomorphic.Scalars.nativeHolomorphicH1Module A.variety.analyticModel A.variety.analyticSpace
    SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.carrier) 1 →ₗ[ℂ]
      CategoryTheory.Sheaf.H (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf A.variety.analyticModel A.variety.analyticSpace) 1 := by
  let U := SheafCohomology.CechFiniteCover.Projective.finiteAffineCoverOpen A
  letI := SheafCohomology.CechScalars.Projective.cechComplexCohomologyModule A (HilbertConstruction.Line.Bundles.structureModule A.carrier) U 1
  letI := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
  letI := Holomorphic.Scalars.nativeHolomorphicH1Module A.variety.analyticModel A.variety.analyticSpace
  letI : (HilbertConstruction.Line.Bundles.structureModule A.carrier).IsQuasicoherent :=
    Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (HilbertConstruction.Line.Bundles.LineBundle.trivial A.carrier)
  exact (cechAnalytificationH1Linear A U (SheafCohomology.CechFiniteCover.Projective.finiteAffineCoverOpen_covers A).iSup_eq_top).comp
    (SheafCohomology.CechLinearComparison.Projective.cechHSuccLinearEquivZariski A (HilbertConstruction.Line.Bundles.structureModule A.carrier) U
      (SheafCohomology.CechFiniteCover.Projective.finiteAffineCoverOpen_covers A) (SheafCohomology.CechFiniteCover.Projective.finiteAffineCoverOpen_affine A) 0).symm.toLinearMap

theorem structureH1Analytification_injective : Function.Injective (structureH1Analytification A) := by
  let U := SheafCohomology.CechFiniteCover.Projective.finiteAffineCoverOpen A
  let := SheafCohomology.CechScalars.Projective.cechComplexCohomologyModule A (HilbertConstruction.Line.Bundles.structureModule A.carrier) U 1
  let := SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
  let : (HilbertConstruction.Line.Bundles.structureModule A.carrier).IsQuasicoherent :=
    Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (HilbertConstruction.Line.Bundles.LineBundle.trivial A.carrier)
  exact (cechAnalytificationH1Linear_injective A U (SheafCohomology.CechFiniteCover.Projective.finiteAffineCoverOpen_covers A).iSup_eq_top).comp
    (SheafCohomology.CechLinearComparison.Projective.cechHSuccLinearEquivZariski A (HilbertConstruction.Line.Bundles.structureModule A.carrier) U
      (SheafCohomology.CechFiniteCover.Projective.finiteAffineCoverOpen_covers A) (SheafCohomology.CechFiniteCover.Projective.finiteAffineCoverOpen_affine A) 0).symm.injective

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CechAnalytificationLinear
