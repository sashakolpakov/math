import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.OrientedPurityRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionResidueRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedFormRestriction

/-! # Adjunction Principal Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionPrincipalRestriction

noncomputable section

/-! The original projective adjunction isomorphisms commute with
principal restriction, using the actual mapped regular equations and
the localized conormal and differential bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FrameAdjunctionEvaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Affine.OrientedPurity.iso
  Affine.DualizingAdjunction.iso Intrinsic.ClosedFormSections.iso
  ConormalAdjunction.equivalence LineValuedKoszulPurity.lineFrame
  LocalAdjunction.ambientIso FrameAdjunctionEvaluation.orientedIsoInFrame
  AffinePrincipal.LineFrame.lineMap

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] [Smooth X.hom]
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B)
  (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (i : Fin (n + 1)) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (r : Γ(IntrinsicOverlap.Intrinsic.space R n, U))

local instance baseAlgebra (W : (IntrinsicOverlap.Intrinsic.space R n).Opens) : Algebra R Γ(IntrinsicOverlap.Intrinsic.space R n, W) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (IntrinsicOverlap.Intrinsic.model R n) W

local instance baseSmooth : Smooth (IntrinsicOverlap.Intrinsic.model R n).hom := SpaceSmooth.smooth

local instance target_quasicoherent :
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (n + 1))

variable {c : ℕ} (s : Fin c → Γ(IntrinsicOverlap.Intrinsic.space R n, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(IntrinsicOverlap.Intrinsic.space R n, U) s = LocalAdjunction.ideal X f U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(IntrinsicOverlap.Intrinsic.space R n, U) (List.ofFn s))
  (e : (AffineOpen.InternalHom.sections U hU).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) ≅
    ModuleCat.of Γ(IntrinsicOverlap.Intrinsic.space R n, U) Γ(IntrinsicOverlap.Intrinsic.space R n, U))

omit [Smooth X.hom] in
theorem line_restriction (x : Γ((LocalAdjunction.dual X f j B).homology c, U)) :
    let N := AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)
    let hIJ := OrientedPurityRestriction.ideal_le X f U hU r
    (LineValuedKoszulPurity.lineFrame Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r)
      (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r))
      ((AffineOpen.InternalHom.sections (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).obj N)
      (AffinePrincipal.LineFrame.targetFrame U hU r N e)).symm
        ((FrameAdjunctionEvaluation.orientedIsoInFrame X f j B hB (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) i
          (((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans hUi)
          (IdealSheafPrincipalEquations.sequence U r s)
          (IdealSheafPrincipalEquations.generates f.left.ker U hU r s hs)
          (IdealSheafPrincipalEquations.weaklyRegular U hU r s hreg)
          (AffinePrincipal.LineFrame.targetFrame U hU r N e)).hom
            (((LocalAdjunction.dual X f j B).homology c).presheaf.map (AffinePrincipal.Sections.inclusion U r).op x)) =
      AffinePrincipal.LineFrame.lineMap U hU r N (LocalAdjunction.ideal X f U hU)
        (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) hIJ
        ((LineValuedKoszulPurity.lineFrame Γ(IntrinsicOverlap.Intrinsic.space R n, U) (LocalAdjunction.ideal X f U hU)
          ((AffineOpen.InternalHom.sections U hU).obj N) e).symm
            ((FrameAdjunctionEvaluation.orientedIsoInFrame X f j B hB U hU i hUi s hs hreg e).hom x)) := by
  dsimp only
  rw [OrientedPurityRestriction.restriction X f j B hB U hU i hUi r s hs hreg e x]
  exact (AffinePrincipal.LineFrame.lineFrame_symm_restriction U hU r
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) e
    (LocalAdjunction.ideal X f U hU) (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r))
    (OrientedPurityRestriction.ideal_le X f U hU r)
    ((FrameAdjunctionEvaluation.orientedIsoInFrame X f j B hB U hU i hUi s hs hreg e).hom x)).symm

variable {g : ℕ} (hc : c + g = n)
  (bI : Module.Basis (Fin c) (LocalAdjunction.quotient X f U hU) (LocalAdjunction.ideal X f U hU).Cotangent)
  (bQ : Module.Basis (Fin g) (LocalAdjunction.quotient X f U hU) Ω[LocalAdjunction.quotient X f U hU⁄R])
  (τ : Type u) [LinearOrder τ]
  [aU : Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [tU : IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [etU : Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  (σ : Type u) [LinearOrder σ]
  [aV : Algebra (MvPolynomial σ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ AffinePrincipal.Sections.openSubset U r))]
  [tV : IsScalarTower R (MvPolynomial σ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ AffinePrincipal.Sections.openSubset U r))]
  [etV : Algebra.Etale (MvPolynomial σ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ AffinePrincipal.Sections.openSubset U r))]

include e τ σ aU tU etU aV tV etV in
theorem restriction (x : Γ((LocalAdjunction.dual X f j B).homology c, U)) :
    (@LocalAdjunction.sectionIso R _ _ n X f _ _ j B hB (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) i
      (((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans hUi) c g hc
      (IdealSheafPrincipalEquations.sequence U r s)
      (IdealSheafPrincipalEquations.generates f.left.ker U hU r s hs)
      (IdealSheafPrincipalEquations.weaklyRegular U hU r s hreg)
      (AdjunctionResidueRestriction.conormalBasis X f U hU r bI)
      (AdjunctionResidueRestriction.quotientBasis X f U hU r bQ) σ _ aV tV etV).hom
        (((LocalAdjunction.dual X f j B).homology c).presheaf.map (AffinePrincipal.Sections.inclusion U r).op x) =
    (Intrinsic.ClosedFormSections.directImage R X (IntrinsicOverlap.Intrinsic.model R n) f g).presheaf.map
      (AffinePrincipal.Sections.inclusion U r).op ((LocalAdjunction.sectionIso X f j B hB U hU i hUi hc s hs hreg bI bQ τ).hom x) := by
  let : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R n, U) := Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R n) U hU
  let : Algebra.Smooth R (LocalAdjunction.quotient X f U hU) := Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R n) f U hU
  let : Algebra.Smooth R Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r) :=
    Intrinsic.SmoothClosedSections.smooth_sections R (IntrinsicOverlap.Intrinsic.model R n) (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)
  let : Algebra.Smooth R (LocalAdjunction.quotient X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) :=
    Intrinsic.SmoothClosedSections.smooth_quotient R X (IntrinsicOverlap.Intrinsic.model R n) f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)
  let N := AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)
  let hIJ := OrientedPurityRestriction.ideal_le X f U hU r
  let a := (FrameAdjunctionEvaluation.orientedIsoInFrame X f j B hB U hU i hUi s hs hreg e).hom x
  let z := (LineValuedKoszulPurity.lineFrame Γ(IntrinsicOverlap.Intrinsic.space R n, U)
    (LocalAdjunction.ideal X f U hU) ((AffineOpen.InternalHom.sections U hU).obj N) e).symm a
  have hline := line_restriction X f j B hB U hU i hUi r s hs hreg e x
  have hv := @FrameAdjunctionEvaluation.sectionIso_apply_frame R _ _ n X f _ _ j B hB (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) i
    (((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans hUi) c
    (IdealSheafPrincipalEquations.sequence U r s)
    (IdealSheafPrincipalEquations.generates f.left.ker U hU r s hs)
    (IdealSheafPrincipalEquations.weaklyRegular U hU r s hreg)
    (AffinePrincipal.LineFrame.targetFrame U hU r N e) g hc
    (AdjunctionResidueRestriction.conormalBasis X f U hU r bI)
    (AdjunctionResidueRestriction.quotientBasis X f U hU r bQ) σ _ aV tV etV
    (((LocalAdjunction.dual X f j B).homology c).presheaf.map (AffinePrincipal.Sections.inclusion U r).op x)
  let iv := @Intrinsic.ClosedFormSections.iso R _ X (IntrinsicOverlap.Intrinsic.model R n) f _
    (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) σ _ aV tV etV g
  have hline' := congrArg
    (fun w : (LocalAdjunction.quotient X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)) ⊗[Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r)]
        ((AffineOpen.InternalHom.sections (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).obj N) =>
      iv.hom (ConormalAdjunction.equivalence (k := R) (R := Γ(IntrinsicOverlap.Intrinsic.space R n, AffinePrincipal.Sections.openSubset U r))
        (LocalAdjunction.ideal X f (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r))
        (AdjunctionResidueRestriction.conormalBasis X f U hU r bI)
        (AdjunctionResidueRestriction.quotientBasis X f U hU r bQ)
        (LocalAdjunction.ambientIso X f j (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) i
          (((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans hUi) hc w))) hline
  have h₁ := hv.trans hline'
  have hr := AdjunctionResidueRestriction.residue_square X f U hU r
    bI bQ j i hUi hc hIJ z
  have h₂ := h₁.trans (congrArg iv.hom hr)
  have hf := @Intrinsic.ClosedFormRestriction.restriction R _ X (IntrinsicOverlap.Intrinsic.model R n) f _ U hU τ _ aU tU etU
    (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) σ _ aV tV etV (AffinePrincipal.Sections.inclusion U r) g
    (ConormalAdjunction.equivalence (k := R) (R := Γ(IntrinsicOverlap.Intrinsic.space R n, U))
      (LocalAdjunction.ideal X f U hU) bI bQ (LocalAdjunction.ambientIso X f j U hU i hUi hc z))
  have h₃ := h₂.trans hf.symm
  have hu := FrameAdjunctionEvaluation.sectionIso_apply_frame X f j B hB U hU i hUi s hs hreg e hc bI bQ τ x
  exact h₃.trans (congrArg
    ((Intrinsic.ClosedFormSections.directImage R X (IntrinsicOverlap.Intrinsic.model R n) f g).presheaf.map (AffinePrincipal.Sections.inclusion U r).op)
    hu.symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionPrincipalRestriction
