import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PointParameterGeometry
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CenteredParameterBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraEquivDifferentialBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DifferentialBasis

/-! # Point Parameter Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PointParameterBasis

noncomputable section

/-! The actual parameters in a principal point neighborhood form the
quotient differential basis, with the same ambient lifts as its equations. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y) [IsClosedImmersion f.left]
  (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)
  (U : Y.left.Opens) (hU : IsAffineOpen U) (hsU : ⊤ ≤ s ⁻¹ᵁ (f.left ⁻¹ᵁ U))
  (σ : Type u) [Fintype σ] [Algebra (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  {m : ℕ} (e : Fin m ≃ σ) (r : Γ(Y.left, U))

def sourceBasis : Module.Basis (Fin m) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ Y.left.basicOpen r))
    Ω[SmoothClosedSections.ring R X (f.left ⁻¹ᵁ Y.left.basicOpen r)⁄R] :=
  AffineOpen.DifferentialBasis.basis R X
    (PointParameterNeighborhood.preimageRestriction R X Y f U r)
    (hU.preimage f.left) ((hU.basicOpen r).preimage f.left)
    (IntegralComparison.Etale.CenteredParameterBasis.basis R (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U)) σ e)

omit [Fintype σ] in
theorem sourceBasis_apply (i : Fin m) : sourceBasis R X Y f U hU σ e r i =
    KaehlerDifferential.D R (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ Y.left.basicOpen r))
      (PointParameterNeighborhood.quotientParameter R X Y f s hs U hsU σ e r i) :=
  AffineOpen.DifferentialBasis.basis_apply R X
    (PointParameterNeighborhood.preimageRestriction R X Y f U r)
    (hU.preimage f.left) ((hU.basicOpen r).preimage f.left)
    (IntegralComparison.Etale.CenteredParameterBasis.basis R (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U)) σ e)
    (fun i => IntegralComparison.Etale.CoordinateSectionKernel.parameter
      (SectionEvaluation.evaluation R X s hs (f.left ⁻¹ᵁ U) hsU) (e i))
    (IntegralComparison.Etale.CenteredParameterBasis.basis_apply R (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U)) σ
      (SectionEvaluation.evaluation R X s hs (f.left ⁻¹ᵁ U) hsU) e) i

def quotientBasis :
    Module.Basis (Fin m) (SmoothClosedSections.ring R Y (Y.left.basicOpen r) ⧸
      f.left.ker.ideal ⟨Y.left.basicOpen r, hU.basicOpen r⟩)
      Ω[SmoothClosedSections.ring R Y (Y.left.basicOpen r) ⧸
        f.left.ker.ideal ⟨Y.left.basicOpen r, hU.basicOpen r⟩⁄R] :=
  AlgebraEquivDifferentialBasis.basis
    (SmoothClosedSections.quotientEquiv R X Y f (Y.left.basicOpen r) (hU.basicOpen r)).symm
    (sourceBasis R X Y f U hU σ e r)

variable {c : ℕ} (a : Fin c → Γ(Y.left, U))
  (D : PointParameterNeighborhood.Data R X Y f s hs U hsU σ a e r)

omit [Fintype σ] in
theorem quotientBasis_apply (i : Fin m) : quotientBasis R X Y f U hU σ e r i =
    KaehlerDifferential.D R (SmoothClosedSections.ring R Y (Y.left.basicOpen r) ⧸
      f.left.ker.ideal ⟨Y.left.basicOpen r, hU.basicOpen r⟩)
      (Ideal.Quotient.mk _ (D.parameter i)) := by
  have h := AlgebraEquivDifferentialBasis.basis_apply
    (SmoothClosedSections.quotientEquiv R X Y f (Y.left.basicOpen r) (hU.basicOpen r)).symm
    (sourceBasis R X Y f U hU σ e r)
    (PointParameterNeighborhood.quotientParameter R X Y f s hs U hsU σ e r)
    (sourceBasis_apply R X Y f s hs U hU hsU σ e r) i
  have ht : (SmoothClosedSections.quotientEquiv R X Y f (Y.left.basicOpen r) (hU.basicOpen r)).symm
      (PointParameterNeighborhood.quotientParameter R X Y f s hs U hsU σ e r i) =
      Ideal.Quotient.mk _ (D.parameter i) := by
    apply (SmoothClosedSections.quotientEquiv R X Y f (Y.left.basicOpen r) (hU.basicOpen r)).injective
    rw [AlgEquiv.apply_symm_apply, SmoothClosedSections.quotientEquiv_mk, D.lift]
  exact h.trans (congrArg (KaehlerDifferential.D R _) ht)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PointParameterBasis
