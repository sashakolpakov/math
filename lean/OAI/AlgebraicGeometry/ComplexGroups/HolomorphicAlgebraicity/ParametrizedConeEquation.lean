import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCoordinateImage
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FinitePullback
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeFiberEquation
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.RootContinuity
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Parametrized Cone Equation -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ParametrizedConeEquation.Constructions.Cone

noncomputable section

/-!
# Full homogeneous equations for scalar images of a parametrized cone

Local parametrizations of the same dimension as a finite normalization
extend the generic equation across every exceptional fiber. Persistence of
roots gives the reverse inclusion. The monic term controls the zero fiber.
-/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

theorem continuous_fiberCoordinates {n : ℕ} :
    Continuous (fun p : (Fin n → ℂ) × ℂ => ConeFiberEquation.Constructions.Cone.fiberCoordinates p.1 p.2) := by
  apply continuous_pi
  intro i
  cases i with
  | none => exact continuous_snd
  | some i => exact (continuous_apply i).comp continuous_fst

theorem exists_full_homogeneous_coordinate_equation
    {E A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]
    {n : ℕ} (hn : 0 < n)
    (hdim : Module.finrank ℂ E = Module.finrank ℂ (Fin n → ℂ))
    {S : Set A} (hzero : 0 ∈ S) (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃v⦄, v ∈ S → c • v ∈ S)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v)
    (L : A →L[ℂ] (Fin n → ℂ)) (hker : ∀ v ∈ S, L v = 0 → v = 0)
    (hfinite : ∀ y, {v | v ∈ S ∧ L v = y}.Finite) (hsurj : L '' S = univ)
    (hparam : ∀ p ∈ S, p ≠ 0 → ∃ (O : Set A) (U : Set E) (φ : E → A),
      IsOpen O ∧ p ∈ O ∧ IsOpen U ∧ DifferentiableOn ℂ φ U ∧
      S ∩ O ⊆ φ '' U ∧ MapsTo φ U S ∧ InjOn φ U)
    (ℓ : A →L[ℂ] ℂ) :
    ∃ (d : ℕ) (F : MvPolynomial (Option (Fin n)) ℂ),
      0 < d ∧ F.IsHomogeneous d ∧ F ≠ 0 ∧
      (∀ y z, (y, z) ∈ (L.prod ℓ) '' S ↔ MvPolynomial.eval (ConeFiberEquation.Constructions.Cone.fiberCoordinates y z) F = 0) ∧
      ∀ z : ℂ, MvPolynomial.eval (ConeFiberEquation.Constructions.Cone.fiberCoordinates 0 z) F = z ^ d := by
  let T := (L.prod ℓ) '' S
  obtain ⟨hT, hconeT, hlocalT, hproperT, hfiniteT, _⟩ :=
    ConeCoordinateImage.Constructions.Cone.coordinate_image_properties hS hcone hlocal L hker hfinite ℓ
  obtain ⟨d, P, hcoeff, hP, hnear⟩ := PuncturedFiberPolynomial.Constructions.Cone.exists_punctured_fiber_polynomial hn hproperT hfiniteT
    (fun p _ hp => hlocalT p hp)
  have hscale (t : ℂ) (ht : t ≠ 0) (x : Fin n → ℂ) (hx : x ≠ 0) :
      P (t • x) = (P x).scaleRoots t := by
    apply ConeCoefficientScaling.Constructions.Cone.fiber_polynomial_scaleRoots (fun c p hp => hconeT c hp) hcoeff hP _ ht hx
    intro y hy
    obtain ⟨V, c, hV, hyV, hV0, hc, hcn, _, hroot⟩ := hnear y hy
    exact ⟨V, c, hV, hyV, hV0, hc, hcn, hroot⟩
  obtain ⟨F, hF, hFeq, hFzero⟩ :=
    ConeFiberEquation.Constructions.Cone.exists_monic_homogeneous_fiber_equation_of_scaling hcoeff hP hscale
  have hFne : F ≠ 0 := by
    intro hz
    have h := hFzero 1
    rw [hz, map_zero, one_pow] at h
    exact zero_ne_one h
  have hd : 0 < d := by
    let x : Fin n → ℂ := fun _ => 1
    have hx : x ≠ 0 := by
      intro hx0
      exact one_ne_zero (congrFun hx0 ⟨0, hn⟩)
    obtain ⟨V, c, _, hxV, hV0, _, _, hdense, hroot⟩ := hnear x hx
    obtain ⟨y, hy, hcy⟩ := (mem_closure_iff_frequently.mp (hdense hxV)).exists
    have hyS : y ∈ L '' S := by rw [hsurj]; exact mem_univ y
    obtain ⟨v, hv, hvy⟩ := hyS
    have hrootv : (P y).eval (ℓ v) = 0 :=
      ((hroot y hy hcy).2 (ℓ v)).mp ⟨v, hv, Prod.ext hvy rfl⟩
    by_contra hdnot
    have hd0 : d = 0 := by omega
    have hPone : P y = 1 := eq_one_of_monic_natDegree_zero (hP y (hV0 hy)).1
      ((hP y (hV0 hy)).2.trans hd0)
    rw [hPone, eval_one] at hrootv
    exact one_ne_zero hrootv
  have hvanish (v : A) (hv : v ∈ S) (hv0 : v ≠ 0) :
      MvPolynomial.eval (ConeFiberEquation.Constructions.Cone.fiberCoordinates (L v) (ℓ v)) F = 0 := by
    have hLv : L v ≠ 0 := fun hz => hv0 (hker v hv hz)
    obtain ⟨V, c, hV, hLvV, hV0, hc, hcn, _, hroot⟩ := hnear (L v) hLv
    have hcont : Continuous (fun w : A => MvPolynomial.eval (ConeFiberEquation.Constructions.Cone.fiberCoordinates (L w) (ℓ w)) F) :=
      F.continuous_eval.comp (continuous_fiberCoordinates.comp (L.prod ℓ).continuous)
    apply FinitePullback.Constructions.Cone.eq_zero_of_generic_finite_local_parametrizations hdim L hfinite hparam hv hv0
      hV hc hLvV hcn hcont.continuousAt
    intro w hw hLw hcw
    rw [hFeq (L w) (hV0 hLw) (ℓ w)]
    exact ((hroot (L w) hLw hcw).2 (ℓ w)).mp ⟨w, hw, rfl⟩
  have hrootmem (y : Fin n → ℂ) (hy : y ≠ 0) (z : ℂ)
      (hz : MvPolynomial.eval (ConeFiberEquation.Constructions.Cone.fiberCoordinates y z) F = 0) : (y, z) ∈ T := by
    obtain ⟨V, c, hV, hyV, hV0, _, _, hdense, hroot⟩ := hnear y hy
    rw [hFeq y hy z] at hz
    exact RootContinuity.Constructions.RootPolynomials.root_mem_closed_set_of_generic_roots hT hV
      (fun j => (hcoeff j).mono hV0) (fun w hw => hP w (hV0 hw)) hdense
      (fun w hw u hu => ((hroot w hw.1 hw.2).2 u).mpr hu) hyV hz
  refine ⟨d, F, hd, hF, hFne, ?_, hFzero⟩
  intro y z
  constructor
  · intro hp
    obtain ⟨v, hv, hvp⟩ := hp
    by_cases hv0 : v = 0
    · have hp0 : (y, z) = 0 := hvp.symm.trans (by rw [hv0, map_zero])
      have hy0 : y = 0 := congrArg Prod.fst hp0
      have hz0 : z = 0 := congrArg Prod.snd hp0
      rw [hy0, hz0, hFzero, zero_pow (Nat.ne_of_gt hd)]
    · have h := hvanish v hv hv0
      have hvy : L v = y := congrArg Prod.fst hvp
      have hvz : ℓ v = z := congrArg Prod.snd hvp
      rwa [hvy, hvz] at h
  · intro hz
    by_cases hy : y = 0
    · subst y
      rw [hFzero] at hz
      have hz0 : z = 0 := eq_zero_of_pow_eq_zero hz
      subst z
      exact ⟨0, hzero, map_zero (L.prod ℓ)⟩
    · exact hrootmem y hy z hz

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ParametrizedConeEquation.Constructions.Cone
