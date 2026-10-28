import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.IntrinsicCoefficientHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.RestrictionNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientLocalPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ProjectiveResolutionFree

/-! # Hom Local -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal

noncomputable section

/-! The original finite-flat coefficient dual resolution is locally
the internal Hom into the actual top-form sheaf. Only ordinary affine
coordinate subopens are needed; the scalar global adjunction supplies
the intrinsic normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
open OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) {Y : Scheme.{u}}
  (f : Y ⟶ X.left) [IsFinite f] [Flat f]
  (i : X ⟶ IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.model R n) [IsClosedImmersion i.left]
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n)

local instance model_finiteType : LocallyOfFiniteType (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.model R n).hom := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType
local instance model_noetherian : IsLocallyNoetherian (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.model R n).left :=
  LocallyOfFiniteType.isLocallyNoetherian (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.model R n).hom

abbrev scalar := Global.StructureUnit.directImage i.left
abbrev coefficient := Cech.StructurePullbackUnit.coefficients f i.left
local instance : (coefficient X f i).IsQuasicoherent := IntegralComparison.Finite.MapPureTrace.coefficients_quasicoherent f i.left
local instance : (coefficient X f i).IsFiniteType := IntegralComparison.Finite.MapPureTrace.coefficients_finiteType f i.left

abbrev scalarComplex := IntegralComparison.Projective.NegativeResolution.complex (scalar X i) j B
abbrev coefficientComplex := IntegralComparison.Projective.NegativeResolution.complex (coefficient X f i) j B
abbrev canonical := AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)
abbrev scalarDual := Affine.LinearResolutionPurity.internalComplex (canonical j) (scalarComplex X i j B)
abbrev coefficientDual := Affine.LinearResolutionPurity.internalComplex (canonical j) (coefficientComplex X f i j B)
abbrev sourceSheaf := (coefficientDual X f i j B).homology (n - g)
abbrev formSheaf := Intrinsic.ClosedFormSections.directImage R X (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.model R n) i g
abbrev targetSheaf := ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (coefficient X f i) (formSheaf X i g)

local instance : (canonical (R := R) j).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (n + 1))
local instance scalar_terms (q : ℕ) : ((scalarComplex X i j B).X q).IsQuasicoherent := inferInstance
local instance coefficient_terms (q : ℕ) : ((coefficientComplex X f i j B).X q).IsQuasicoherent := inferInstance
include hB in
omit [IsProper X.hom] in
theorem scalar_dual_terms (q : ℕ) : ((scalarDual X i j B).X q).IsQuasicoherent :=
  IntegralComparison.Projective.InternalHomCoherence.term (scalar X i) j B (n + 1) hB q
include hB in
omit [Flat f] [IsProper X.hom] in
theorem coefficient_dual_terms (q : ℕ) : ((coefficientDual X f i j B).X q).IsQuasicoherent :=
  IntegralComparison.Projective.InternalHomCoherence.term (coefficient X f i) j B (n + 1) hB q

def scalarAdjunction : (scalarDual X i j B).homology (n - g) ≅ formSheaf X i g := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  exact IntegralComparison.Projective.AdjunctionGlobal.iso X i g j B hB hg

attribute [local instance] IntegralComparison.Finite.FlatCoefficientSections.quotientAlgebra IntegralComparison.Finite.FlatCoefficientSections.coefficientAlgebra IntegralComparison.Finite.FlatCoefficientSections.ambientAlgebra

variable (U : (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)

include hU in
omit [Flat f] [IsProper X.hom] in
theorem coefficient_finite : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i.left U) := by
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian i.left
  exact IntegralComparison.Finite.FlatCoefficientSections.finite f i.left U hU
include hU in
omit [IsProper X.hom] in
theorem coefficient_projective : Module.Projective (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i.left U) := by
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian i.left
  exact IntegralComparison.Finite.FlatCoefficientSections.projective f i.left U hU
local instance formScalar : Module (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) Γ(formSheaf X i g, U) :=
  inferInstanceAs (Module Γ(X.left, i.left ⁻¹ᵁ U)
    Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g, i.left ⁻¹ᵁ U))
local instance formTower : IsScalarTower Γ(IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.space R n, U) (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) Γ(formSheaf X i g, U) where
  smul_assoc a b x := by
    change (algebraMap Γ(IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.space R n, U) (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) a * b) • x =
      algebraMap Γ(IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.space R n, U) (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) a • (b • x)
    exact mul_smul _ _ _

variable (k : Fin (n + 1)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)

include hUk in
omit [IsProper X.hom] in
theorem scalar_projective (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((scalarComplex X i j B).X q)) :=
  Affine.ProjectiveResolutionTerms.term_projective U hU k hUk (scalar X i) j B q
include hUk in
omit [Flat f] [IsProper X.hom] in
theorem coefficient_term_projective (q : ℕ) :
    Projective ((AffineOpen.InternalHom.sections U hU).obj ((coefficientComplex X f i j B).X q)) :=
  Affine.ProjectiveResolutionTerms.term_projective U hU k hUk (coefficient X f i) j B q

def sectionIso :
    (Affine.ModuleExactSections.sections U).obj (sourceSheaf X f i g j B) ≅
      (Affine.ModuleExactSections.sections U).obj (targetSheaf X f i g) := by
  letI := formScalar X i g U
  letI := formTower X i g U
  letI (q : ℕ) := scalar_dual_terms X i j B hB q
  letI (q : ℕ) := coefficient_dual_terms X f i j B hB q
  letI := coefficient_finite X f i U hU
  letI := coefficient_projective X f i U hU
  letI (q : ℕ) := scalar_projective X i j B U hU k hUk q
  letI (q : ℕ) := coefficient_term_projective X f i j B U hU k hUk q
  exact Affine.IntrinsicCoefficientHom.iso U hU (canonical j)
    (scalarComplex X i j B) (coefficientComplex X f i j B) (scalar X i) (coefficient X f i)
    (IntegralComparison.Projective.NegativeResolution.augmentation (scalar X i) j B)
    (IntegralComparison.Projective.NegativeResolution.augmentation (coefficient X f i) j B)
    (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (i.left.app_surjective U hU) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i.left U)
    (FiniteCoefficient.RestrictionNormalization.scalarChartIso i.left U hU)
    (IntegralComparison.Finite.FlatCoefficientSections.chartIso f i.left U hU) (n - g) (formSheaf X i g)
    (scalarAdjunction X i g j B hB hg)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal
