import OAI.RepresentationTheory.Theta.Geometric.Reference.ProjectorCommutation
import OAI.RepresentationTheory.Theta.Geometric.ComponentCovariance

/-! # Covariance -/

namespace OAI.RepresentationTheory.Theta.Geometric.Covariance

noncomputable section

/-! The canonical theta lift is fixed by the original component projector.
Full raw Hecke covariance follows on its component and on the complement. -/
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
namespace ActiveHeckeThetaData
variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [IsTopologicalGroup Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
    (hc : D.HasFiniteCoordinates) (hArithmetic : DenseRange D.rationalFinite)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace)
    (hcover : D.IsPeriodUniformization X cover)
    (href : ∀ x, D.totalPeriodMap j X component cover x = D.referenceModuliMap hg x)
    (hh : D.HasHolomorphicThetaData) (ha : D.HasRationalThetaCovariance)

local notation "Θ" => D.thetaAlbaneseLift hg j X component cover hcover hh ha
local notation "e" => OAI.RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished
local notation "active" => OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e

omit [IsTopologicalGroup Ga] in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.thetaAlbaneseLift_projector (φ : D.sphericalInputs) : D.ballFormsProjector j (Θ φ) = Θ φ := by
  apply D.albanesePullback_injective hg
  apply D.componentForms_jointly_injective hg
  intro i
  rw [D.ballFormsProjector_component]
  by_cases hij : i = j
  · simp only [hij, ite_true]
  · rw [ite_eq_right hij, D.thetaAlbaneseLift_complement hg j X component cover hcover hh ha i hij φ]

include hA hdegree hs hc hArithmetic href in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.original_raw_theta_covariance (a : Intrinsic.Hecke.ActiveWeight) (T : SphericalGU.Spherical.SL3Hecke q)
    (hT : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (SphericalGU.Spherical.integralSL3 q) (Intrinsic.Hecke.activeSLRepresentative q a) T)
    (φ : D.sphericalInputs) :
    D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) (Θ φ) =
      Θ (D.sphericalWeil T φ) := by
  let c := D.totalPeriodMap j X component cover
  have hcont := D.totalPeriodMap_continuous j X component cover hcover.2.1.continuous
  let : Finite (D.ClearedBranch c a) := D.clearedBranch_finite hg hcont a
  let : Fintype (D.ClearedBranch c a) := Fintype.ofFinite _
  obtain ⟨β, hβ⟩ := D.original_active_branch_bijection hg hgood hIsogenyQuotient A hA hdegree hs hc hArithmetic
    j X component cover hcover href a
  choose g hcos haway htarget using hβ
  have hprincipal := D.activeTheta_algebraic_component_covariance hg hgood hIsogenyQuotient A hA
    j X component cover hcover hh ha a T hT β g hcos haway htarget φ
  have hcomm := LinearMap.congr_fun
    (D.activeForms_projector_commute hg hgood hIsogenyQuotient A hA hdegree hs hc hArithmetic
      j X component cover hcover href a) (Θ φ)
  have hfixed : D.ballFormsProjector j
      (D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) (Θ φ)) =
    D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) (Θ φ) := by
    simp only [LinearMap.comp_apply] at hcomm
    rw [D.thetaAlbaneseLift_projector hg j X component cover hcover hh ha φ] at hcomm
    exact hcomm.symm
  apply D.albanesePullback_injective hg
  apply D.componentForms_jointly_injective hg
  intro i
  by_cases hij : i = j
  · subst i
    have hinj : Function.Injective (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback component.hom) :=
      (show Function.LeftInverse (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback component.inv) (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback component.hom) from
        InverseCentralFormPowers.formsPullback_iso_cancel component).injective
    simp only [AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp, LinearMap.comp_apply] at hprincipal
    exact hinj hprincipal
  · have H := D.ballFormsProjector_component hg i j
      (D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) (Θ φ))
    rw [hfixed, ite_eq_right hij] at H
    exact H.trans (D.thetaAlbaneseLift_complement hg j X component cover hcover hh ha i hij
      (D.sphericalWeil T φ)).symm

include hA hdegree hs hc hArithmetic href in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.original_rational_theta_covariance (T : SphericalGU.Spherical.SL3Hecke q) (φ : D.sphericalInputs) :
    D.heckeRationalForms hg A (active T) (Θ φ) = Θ (D.sphericalWeil T φ) := by
  choose B hB hmatch using Active.Basis.Spherical.active_basis_matching q D.pel.reference.distinguished A.basis hA.basis
  apply Complexify.covariance_of_span Θ D.sphericalWeilLinear
    ((D.heckeRationalForms hg A).comp (active).toLinearMap) B
    (Active.Cartan.Spherical.active_raw_span q B hB) _ T φ
  intro a ψ
  change D.heckeRationalForms hg A (active (B a)) (Θ ψ) = Θ (D.sphericalWeil (B a) ψ)
  rw [hmatch]
  exact D.original_raw_theta_covariance hg hgood hIsogenyQuotient A hA hdegree hs hc hArithmetic
    j X component cover hcover href hh ha a (B a) (hB a) ψ

include hA hdegree hs hc hArithmetic href in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.original_complex_theta_covariance (h : ℂ ⊗[ℚ] SphericalGU.Spherical.SL3Hecke q) (φ : D.sphericalInputs) :
    D.activeFormsComplex (D.heckeRationalForms hg A) e h (Θ φ) = Θ (D.sphericalWeilComplex h φ) := by
  unfold Data.ActiveHeckeThetaData.activeFormsComplex Data.ActiveHeckeThetaData.sphericalWeilComplex
  apply Complexify.covariance_extends_to_complex (A := SphericalGU.Spherical.SL3Hecke q)
    (S := D.sphericalInputs) (V := D.pel.OneFormsA) Θ D.sphericalWeilLinear
    ((D.heckeRationalForms hg A).comp (active).toLinearMap) _ h φ
  exact D.original_rational_theta_covariance hg hgood hIsogenyQuotient A hA hdegree hs hc hArithmetic
    j X component cover hcover href hh ha

end ActiveHeckeThetaData

end

end OAI.RepresentationTheory.Theta.Geometric.Covariance
