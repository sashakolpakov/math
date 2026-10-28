import OAI.Geometry.ComplexTorus.RiemannProjectivity.BoundedPolynomial
import OAI.Geometry.ComplexTorus.RiemannProjectivity.RootContinuityAt
import OAI.Geometry.ComplexTorus.RiemannProjectivity.SeparableFibersExists

/-! # Local Fiber -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalFiber.Constructions.LocalFiberExtension

noncomputable section

/-!
# RiemannProjectivity: local equations extend through branching without adding points

A generic monic equation for finite analytic fibers extends holomorphically
across its exceptional set. All roots of the extended equation belong to
the original closed set. Equality on exceptional fibers requires the
separate assertion that those fibers are approached by generic fibers.
-/

open Set Filter _root_.Metric _root_.Polynomial
open scoped _root_.Topology

theorem exists_separable_extended_equation {n : ℕ} {S : Set ((Fin n → ℂ) × ℂ)}
    (hS : IsClosed S) {x : Fin n → ℂ} {z₀ : ℂ}
    (hlocal : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, z₀))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite) :
    ∃ (R : ℝ) (k : ℕ) (U : Set (Fin n → ℂ))
        (P : (Fin n → ℂ) → ℂ[X]) (c : (Fin n → ℂ) → ℂ),
      0 < R ∧ IsOpen U ∧ x ∈ U ∧ DifferentiableOn ℂ c U ∧
      U ⊆ closure {y | y ∈ U ∧ c y ≠ 0} ∧
      (∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) U) ∧
      (∀ y, (P y).Monic ∧ (P y).natDegree = k) ∧
      (∀ y ∈ U, ∀ z, (P y).eval z = 0 → (y, z) ∈ S) ∧
      ∀ y ∈ U, c y ≠ 0 → (P y).Separable ∧
        ∀ z ∈ closedBall z₀ R, (y, z) ∈ S ↔ (P y).eval z = 0 := by
  obtain ⟨R, k, V, Q, c, hR, hV, hxV, hc, hdense, hQcoeff, hQ⟩ :=
    SeparableFibersExists.Constructions.SeparableFibers.exists_generic_equation hlocal hfinite
  have hn : ¬∀ᶠ y in 𝓝 x, c y = 0 := by
    intro hz
    obtain ⟨y, hy, hcy⟩ := ((mem_closure_iff_frequently.mp (hdense hxV)).and_eventually hz).exists
    exact hy.2 hcy
  have hb (y : Fin n → ℂ) (hy : y ∈ V) (hcy : c y ≠ 0)
      (z : ℂ) (hz : (Q y).eval z = 0) : ‖z‖ ≤ R + ‖z₀‖ := by
    have hd : dist z z₀ < R := mem_ball.mp ((hQ y hy hcy).2.2.2.1 z hz)
    have ht := dist_triangle z z₀ 0
    simp only [dist_zero_right] at ht
    linarith
  obtain ⟨P, U, hU, hxU, hUV, hPcoeff, hP, hPQ⟩ :=
    BoundedPolynomial.Constructions.BoundedPolynomialExtension.exists_extension hV hc hxV hn k hQcoeff
      (fun y hy hcy => ⟨(hQ y hy hcy).1, (hQ y hy hcy).2.1⟩) hb
  have hdenseU : U ⊆ closure {y | y ∈ U ∧ c y ≠ 0} := by
    intro y hy
    apply mem_closure_iff_frequently.mpr
    exact ((mem_closure_iff_frequently.mp (hdense (hUV hy))).and_eventually
      (hU.mem_nhds hy)).mono (fun _ hz => ⟨hz.2, hz.1.2⟩)
  have hrootS (y : Fin n → ℂ) (hy : y ∈ U) (hcy : c y ≠ 0)
      (z : ℂ) (hz : (P y).eval z = 0) : (y, z) ∈ S := by
    rw [hPQ y hy hcy] at hz
    exact ((hQ y (hUV hy) hcy).2.2.2.2 z
      (ball_subset_closedBall ((hQ y (hUV hy) hcy).2.2.2.1 z hz))).mpr hz
  refine ⟨R, k, U, P, c, hR, hU, hxU, hc.mono hUV, hdenseU, hPcoeff, hP, ?_, ?_⟩
  · intro y hy z hz
    exact RootContinuityAt.Constructions.RootClosure.root_mem_closed hS k hP (hdenseU hy)
      (fun j => ((hPcoeff j).differentiableAt (hU.mem_nhds hy)).continuousAt)
      (fun w hw => hrootS w hw.1 hw.2) hz
  · intro y hy hcy
    rw [hPQ y hy hcy]
    exact ⟨(hQ y (hUV hy) hcy).2.2.1, (hQ y (hUV hy) hcy).2.2.2.2⟩

theorem exists_extended_equation {n : ℕ} {S : Set ((Fin n → ℂ) × ℂ)}
    (hS : IsClosed S) {x : Fin n → ℂ} {z₀ : ℂ}
    (hlocal : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, z₀))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite) :
    ∃ (R : ℝ) (k : ℕ) (U : Set (Fin n → ℂ))
        (P : (Fin n → ℂ) → ℂ[X]) (c : (Fin n → ℂ) → ℂ),
      0 < R ∧ IsOpen U ∧ x ∈ U ∧ DifferentiableOn ℂ c U ∧
      U ⊆ closure {y | y ∈ U ∧ c y ≠ 0} ∧
      (∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) U) ∧
      (∀ y, (P y).Monic ∧ (P y).natDegree = k) ∧
      (∀ y ∈ U, ∀ z, (P y).eval z = 0 → (y, z) ∈ S) ∧
      ∀ y ∈ U, c y ≠ 0 → ∀ z ∈ closedBall z₀ R,
        (y, z) ∈ S ↔ (P y).eval z = 0 := by
  obtain ⟨R, k, U, P, c, hR, hU, hxU, hc, hdense, hcoeff, hP, hroot, heq⟩ :=
    exists_separable_extended_equation hS hlocal hfinite
  exact ⟨R, k, U, P, c, hR, hU, hxU, hc, hdense, hcoeff, hP, hroot,
    fun y hy hcy => (heq y hy hcy).2⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalFiber.Constructions.LocalFiberExtension
