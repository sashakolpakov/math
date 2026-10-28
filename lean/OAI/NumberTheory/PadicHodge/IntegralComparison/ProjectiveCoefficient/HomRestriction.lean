import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.CoefficientHomRestriction

/-! # Hom Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomRestriction

noncomputable section

/-! The local finite-flat coefficient duality of the original projective
resolutions is independent of the auxiliary affine coordinate and
commutes with the literal principal restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) {Y : Scheme.{u}}
  (f : Y ⟶ X.left) [IsFinite f] [Flat f]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R n) [IsClosedImmersion i.left]
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (k : Fin (n + 1)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)

theorem independent (k' : Fin (n + 1)) (hUk' : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k') :
    HomLocal.sectionIso X f i g j B hB hg U hU k hUk = HomLocal.sectionIso X f i g j B hB hg U hU k' hUk' := rfl

attribute [local instance] IntegralComparison.Finite.FlatCoefficientSections.quotientAlgebra IntegralComparison.Finite.FlatCoefficientSections.coefficientAlgebra IntegralComparison.Finite.FlatCoefficientSections.ambientAlgebra
attribute [local instance] HomLocal.formScalar HomLocal.formTower
attribute [local instance] HomLocal.scalar_terms HomLocal.coefficient_terms

include hB hg in
theorem restriction (r : Γ(Projective.IntrinsicOverlap.Intrinsic.space R n, U))
    (z : Γ(HomLocal.sourceSheaf X f i g j B, U)) :
    (HomLocal.sectionIso X f i g j B hB hg (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) k
      (((Projective.IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans hUk)).hom
        ((HomLocal.sourceSheaf X f i g j B).presheaf.map (AffinePrincipal.Sections.inclusion U r).op z) =
      (HomLocal.targetSheaf X f i g).presheaf.map (AffinePrincipal.Sections.inclusion U r).op
        ((HomLocal.sectionIso X f i g j B hB hg U hU k hUk).hom z) := by
  let V := AffinePrincipal.Sections.openSubset U r
  have hV : IsAffineOpen V := hU.basicOpen r
  have hVk : V ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k := ((Projective.IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans hUk
  let : (HomLocal.coefficient X f i).IsQuasicoherent := IntegralComparison.Finite.MapPureTrace.coefficients_quasicoherent f i.left
  let : (HomLocal.coefficient X f i).IsFiniteType := IntegralComparison.Finite.MapPureTrace.coefficients_finiteType f i.left
  let : (HomLocal.canonical (R := R) j).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (n + 1))
  let := HomLocal.formScalar X i g U
  let := HomLocal.formTower X i g U
  let := HomLocal.formScalar X i g V
  let := HomLocal.formTower X i g V
  let (q : ℕ) := HomLocal.scalar_dual_terms X i j B hB q
  let (q : ℕ) := HomLocal.coefficient_dual_terms X f i j B hB q
  let := HomLocal.coefficient_finite X f i U hU
  let := HomLocal.coefficient_projective X f i U hU
  let := HomLocal.coefficient_finite X f i V hV
  let := HomLocal.coefficient_projective X f i V hV
  let (q : ℕ) := HomLocal.scalar_projective X i j B U hU k hUk q
  let (q : ℕ) := HomLocal.coefficient_term_projective X f i j B U hU k hUk q
  let (q : ℕ) := HomLocal.scalar_projective X i j B V hV k hVk q
  let (q : ℕ) := HomLocal.coefficient_term_projective X f i j B V hV k hVk q
  let (q : ℕ) : Module.Free Γ(Projective.IntrinsicOverlap.Intrinsic.space R n, U) ((AffineOpen.InternalHom.sections U hU).obj ((HomLocal.scalarComplex X i j B).X q)) :=
    Affine.ProjectiveResolutionFree.term_free U hU k hUk (HomLocal.scalar X i) j B q
  let (q : ℕ) : Module.Finite Γ(Projective.IntrinsicOverlap.Intrinsic.space R n, U) ((AffineOpen.InternalHom.sections U hU).obj ((HomLocal.scalarComplex X i j B).X q)) :=
    Affine.ProjectiveResolutionFree.term_finite U hU k hUk (HomLocal.scalar X i) j B q
  let (q : ℕ) : Module.Free Γ(Projective.IntrinsicOverlap.Intrinsic.space R n, U) ((AffineOpen.InternalHom.sections U hU).obj ((HomLocal.coefficientComplex X f i j B).X q)) :=
    Affine.ProjectiveResolutionFree.term_free U hU k hUk (HomLocal.coefficient X f i) j B q
  let (q : ℕ) : Module.Finite Γ(Projective.IntrinsicOverlap.Intrinsic.space R n, U) ((AffineOpen.InternalHom.sections U hU).obj ((HomLocal.coefficientComplex X f i j B).X q)) :=
    Affine.ProjectiveResolutionFree.term_finite U hU k hUk (HomLocal.coefficient X f i) j B q
  exact Intrinsic.CoefficientHomRestriction.restriction U hU (HomLocal.canonical j)
    (HomLocal.scalarComplex X i j B) (HomLocal.coefficientComplex X f i j B) (HomLocal.scalar X i) (HomLocal.coefficient X f i)
    (Projective.NegativeResolution.augmentation (HomLocal.scalar X i) j B)
    (Projective.NegativeResolution.augmentation (HomLocal.coefficient X f i) j B)
    (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (i.left.app_surjective U hU) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i.left U)
    (FiniteCoefficient.RestrictionNormalization.scalarChartIso i.left U hU)
    (IntegralComparison.Finite.FlatCoefficientSections.chartIso f i.left U hU) (n - g) (HomLocal.formSheaf X i g)
    (HomLocal.scalarAdjunction X i g j B hB hg) r
    (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left V) (i.left.app_surjective V hV) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f i.left V)
    (FiniteCoefficient.RestrictionNormalization.scalarChartIso i.left V hV)
    (IntegralComparison.Finite.FlatCoefficientSections.chartIso f i.left V hV)
    (FiniteCoefficient.RestrictionNormalization.multiplication f i.left U hU r)
    (Projective.ClosedImmersionPurity.targetTrivialization j (n + 1) U hU k hUk) z

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomRestriction
