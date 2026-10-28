import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ConcatenatedRegularityQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.CompositeSectionKernelImage
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraEquivRegularSequence
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraEquivDifferentialBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Ideal

/-! # Parameter Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterSource

noncomputable section

/-! The literal pullbacks of projective point parameters generate the
actual source section ideal and have their matching differential basis. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {N : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R N)
  [IsClosedImmersion f.left] (z : Spec (CommRingCat.of R) ⟶ X.left)
  (g : ℕ) (U : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hU : IsAffineOpen U)
  (D : PointParameterData.Chart.ParameterData X f z g U hU)

local instance sourceAmbientAlgebra : Algebra R Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (Projective.IntrinsicOverlap.Intrinsic.model R N) U

def parameters : Fin g → Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U) :=
  fun a => f.left.app U (D.parameters a)

omit [IsNoetherianRing R] in
theorem quotient_parameters (j : Fin g) :
    Intrinsic.SmoothClosedSections.quotientEquiv R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f U hU
      (Ideal.Quotient.mk (Projective.LocalAdjunction.ideal X f U hU) (D.parameters j)) = ParameterSource.parameters X f z g U hU D j := rfl

theorem span : Ideal.span (Set.range (ParameterSource.parameters X f z g U hU D)) =
    z.ker.ideal ⟨f.left ⁻¹ᵁ U, hU.preimage f.left⟩ := by
  let a := (f.left.app U).hom
  let b := (z.app (f.left ⁻¹ᵁ U)).hom
  have hn : Ideal.span (Set.range D.equations) = RingHom.ker a := by
    simpa only [a, Scheme.Hom.ker_apply] using D.generates
  have hp : Ideal.span (Set.range (Fin.append D.equations D.parameters)) =
      RingHom.ker (b.comp a) := by
    simpa only [KoszulPoint.Ideal.append, Scheme.Hom.ker_apply, Scheme.Hom.comp_app,
      CommRingCat.hom_comp, a, b] using D.point_generates
  have hs := CompositeSectionKernelImage.image_kernel a (f.left.app_surjective U hU)
    b D.equations D.parameters hn hp
  change Ideal.span (Set.range (fun j => a (D.parameters j))) = _
  exact hs.trans (z.ker_apply ⟨f.left ⁻¹ᵁ U, hU.preimage f.left⟩).symm

omit [IsNoetherianRing R] in
theorem regular : RingTheory.Sequence.IsWeaklyRegular
    (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
    (List.ofFn (ParameterSource.parameters X f z g U hU D)) := by
  let e := Intrinsic.SmoothClosedSections.quotientEquiv R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f U hU
  have hq := Koszul.ConcatenatedRegularityQuotient.quotient_of_append
    (Projective.LocalAdjunction.ideal X f U hU) D.equations D.parameters D.generates D.point_regular
  have ht := AlgebraEquivRegularSequence.regular e.toRingEquiv
    (fun j => Ideal.Quotient.mk (Projective.LocalAdjunction.ideal X f U hU) (D.parameters j)) hq
  change RingTheory.Sequence.IsWeaklyRegular
    (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
    (List.ofFn (fun j => e (Ideal.Quotient.mk (Projective.LocalAdjunction.ideal X f U hU) (D.parameters j)))) at ht
  have heq : (fun j => e (Ideal.Quotient.mk (Projective.LocalAdjunction.ideal X f U hU) (D.parameters j))) =
      ParameterSource.parameters X f z g U hU D := by
    funext j
    exact quotient_parameters X f z g U hU D j
  rw [heq] at ht
  exact ht

def basis : Module.Basis (Fin g)
    (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
    Ω[Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U)⁄R] :=
  AlgebraEquivDifferentialBasis.basis
    (Intrinsic.SmoothClosedSections.quotientEquiv R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f U hU) D.quotientBasis

omit [IsNoetherianRing R] in
theorem basis_apply (j : Fin g) : basis X f z g U hU D j =
    KaehlerDifferential.D R (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
      (ParameterSource.parameters X f z g U hU D j) := by
  have h := AlgebraEquivDifferentialBasis.basis_apply
    (Intrinsic.SmoothClosedSections.quotientEquiv R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f U hU) D.quotientBasis
    (fun j => Ideal.Quotient.mk (Projective.LocalAdjunction.ideal X f U hU) (D.parameters j)) D.quotientBasis_apply j
  exact h.trans (congrArg (KaehlerDifferential.D R _)
    (quotient_parameters X f z g U hU D j))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterSource
