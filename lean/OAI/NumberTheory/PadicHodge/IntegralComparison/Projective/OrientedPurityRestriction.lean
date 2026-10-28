import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.OrientedPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FrameAdjunctionEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ProjectiveResolutionFree
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.QuotientNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.LineFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.IdealSheafPrincipalEquations

/-! # Oriented Purity Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.OrientedPurityRestriction

noncomputable section

/-! The scalar purity coordinate of the original projective resolution
restricts by the actual closed-immersion quotient map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FrameAdjunctionEvaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Affine.OrientedPurity.iso

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] [Smooth X.hom]
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B)
  (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (i : Fin (n + 1)) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (r : Γ(IntrinsicOverlap.Intrinsic.space R n, U))

local instance target_quasicoherent :
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (n + 1))

omit [IsNoetherianRing R] [IsClosedImmersion (Over.Hom.left f)] [Smooth X.hom] in
theorem ideal_le : LocalAdjunction.ideal X f U hU ≤
    (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).comap
      (algebraMap Γ(IntrinsicOverlap.Intrinsic.space R n, U) Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r)) :=
  f.left.ker.ideal_le_comap_ideal
    (U := ⟨AffinePrincipal.Sections.openSubset U r, hU.basicOpen r⟩) (V := ⟨U, hU⟩) ((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r)

variable {c : ℕ} (s : Fin c → Γ(IntrinsicOverlap.Intrinsic.space R n, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(IntrinsicOverlap.Intrinsic.space R n, U) s = LocalAdjunction.ideal X f U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(IntrinsicOverlap.Intrinsic.space R n, U) (List.ofFn s))
  (e : (AffineOpen.InternalHom.sections U hU).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) ≅
    ModuleCat.of Γ(IntrinsicOverlap.Intrinsic.space R n, U) Γ(IntrinsicOverlap.Intrinsic.space R n, U))

omit [Smooth X.hom] in
theorem restriction (x : Γ((LocalAdjunction.dual X f j B).homology c, U)) :
    (FrameAdjunctionEvaluation.orientedIsoInFrame X f j B hB (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) i
      (((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans hUi)
      (IdealSheafPrincipalEquations.sequence U r s)
      (IdealSheafPrincipalEquations.generates f.left.ker U hU r s hs)
      (IdealSheafPrincipalEquations.weaklyRegular U hU r s hreg)
      (AffinePrincipal.LineFrame.targetFrame U hU r
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) e)).hom
        (((LocalAdjunction.dual X f j B).homology c).presheaf.map (AffinePrincipal.Sections.inclusion U r).op x) =
    Ideal.quotientMap (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r))
      (algebraMap Γ(IntrinsicOverlap.Intrinsic.space R n, U) Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r)) (ideal_le X f U hU r)
      ((FrameAdjunctionEvaluation.orientedIsoInFrame X f j B hB U hU i hUi s hs hreg e).hom x) := by
  let (q : ℕ) : Module.Free Γ(IntrinsicOverlap.Intrinsic.space R n, U) ((AffineOpen.InternalHom.sections U hU).obj ((LocalAdjunction.source X f j B).X q)) :=
    Affine.ProjectiveResolutionFree.term_free U hU i hUi (LocalAdjunction.structureImage X f) j B q
  let (q : ℕ) : Module.Finite Γ(IntrinsicOverlap.Intrinsic.space R n, U) ((AffineOpen.InternalHom.sections U hU).obj ((LocalAdjunction.source X f j B).X q)) :=
    Affine.ProjectiveResolutionFree.term_finite U hU i hUi (LocalAdjunction.structureImage X f) j B q
  let (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj ((LocalAdjunction.source X f j B).X q)) :=
    Affine.ProjectiveResolutionTerms.term_projective U hU i hUi (LocalAdjunction.structureImage X f) j B q
  let (q : ℕ) : Projective
      ((AffineOpen.InternalHom.sections (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).obj ((LocalAdjunction.source X f j B).X q)) :=
    Affine.ProjectiveResolutionTerms.term_projective (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) i
      (((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans hUi) (LocalAdjunction.structureImage X f) j B q
  let (q : ℕ) : ((Affine.LinearResolutionPurity.internalComplex
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) (LocalAdjunction.source X f j B)).X q).IsQuasicoherent :=
    LocalDualLine.term_quasicoherent f.left j B (n + 1) hB q
  have he := AffinePrincipal.QuotientNormalization.chart_square f.left U hU r
  have h := AffinePrincipal.OrientedPurity.restriction U hU r
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) (LocalAdjunction.source X f j B)
    (LocalAdjunction.structureImage X f) (NegativeResolution.augmentation (LocalAdjunction.structureImage X f) j B)
    (LocalAdjunction.ideal X f U hU) (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) (ideal_le X f U hU r)
    (LocalAdjunction.quotientSectionIso X f U hU) (LocalAdjunction.quotientSectionIso X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) he
    s hs (IdealSheafPrincipalEquations.generates f.left.ker U hU r s hs) hreg e x
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.OrientedPurityRestriction
