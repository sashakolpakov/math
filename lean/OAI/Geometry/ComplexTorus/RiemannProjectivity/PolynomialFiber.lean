import OAI.Geometry.ComplexTorus.RiemannProjectivity.GlueReduced
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ReducedFamiliesOn
import OAI.Geometry.ComplexTorus.RiemannProjectivity.PolynomialExtensionOf

/-! # Polynomial Fiber -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.PolynomialFiber.Constructions.PolynomialFiberCoefficients

noncomputable section

/-!
# RiemannProjectivity: actual polynomial coefficients for a proper finite cone projection

Canonical local equations glue on the punctured base. Their uniform degree
and root bounds give polynomial growth, so scalar extension at the vertex
produces actual multivariable polynomial coefficients.
-/

open Set _root_.Polynomial

theorem exists_coefficients {d N : ℕ} {S : Set ((Fin (d + 1) → ℂ) × ℂ)}
    (hproper : IsProperMap (fun p : S => p.val.1))
    (hfinite : ∀ x, {z : ℂ | (x, z) ∈ S}.Finite)
    (hlocal : ∀ x, x ≠ 0 → ∀ z, (x, z) ∈ S →
      PeriodWhole.Constructions.PeriodCoordinateEquations.HasLocalMonicEquation S x z)
    (hcard : ∀ x, x ≠ 0 → {z : ℂ | (x, z) ∈ S}.ncard ≤ N)
    {C : ℝ} (hroot : ∀ x, x ≠ 0 → ∀ z, (x, z) ∈ S → ‖z‖ ≤ C * ‖x‖) :
    ∃ (Q : (Fin (d + 1) → ℂ) → ℂ[X]) (A : ℕ → MvPolynomial (Fin (d + 1)) ℂ),
      (∀ j x, x ≠ 0 → MvPolynomial.eval x (A j) = (Q x).coeff j) ∧
      (∀ x, x ≠ 0 → (Q x).Monic ∧ (Q x).natDegree ≤ N ∧
        ∀ z, (x, z) ∈ S ↔ (Q x).eval z = 0) ∧
      ∀ j x, ‖MvPolynomial.eval x (A j)‖ ≤
        ((N.choose j : ℝ) * (max 1 C) ^ N) * (max 1 ‖x‖) ^ N := by
  have hloc : ∀ x ∈ ({x | x ≠ 0} : Set (Fin (d + 1) → ℂ)),
      ∃ (U : Set (Fin (d + 1) → ℂ)) (P : (Fin (d + 1) → ℂ) → ℂ[X]),
        IsOpen U ∧ x ∈ U ∧ U ⊆ {x | x ≠ 0} ∧ ReducedFamiliesOn.Constructions.ReducedFamilies.On S U P := by
    intro x hx
    obtain ⟨U, P, hU, hxU, hP⟩ :=
      ReducedFamiliesOn.Constructions.ReducedFamilies.exists_local hproper (hfinite x) (hlocal x hx)
    exact ⟨U ∩ {x | x ≠ 0}, P, hU.inter isOpen_compl_singleton, ⟨hxU, hx⟩,
      inter_subset_right, hP.mono inter_subset_left⟩
  obtain ⟨Q, hQc, hQm, hQr, hQlocal⟩ := GlueReduced.Constructions.GlueReducedFamilies.exists_global hloc
  have hQd (x : Fin (d + 1) → ℂ) (hx : x ≠ 0) : (Q x).natDegree ≤ N := by
    obtain ⟨U, hU, hxU, hUsub, hOn⟩ := hQlocal x hx
    exact ReducedFamiliesOn.Constructions.ReducedDegree.natDegree_le hU hOn (fun y hy => hcard y (hUsub hy)) hxU
  have hQroot (x : Fin (d + 1) → ℂ) (hx : x ≠ 0) (z : ℂ) (hz : (Q x).eval z = 0) :
      ‖z‖ ≤ C * ‖x‖ := hroot x hx z ((hQr x hx z).mpr hz)
  have hb := fun j => ReducedFamiliesOn.Constructions.ReducedDegree.coefficient_growth hQm hQd hQroot j
  have hpoly (j : ℕ) : ∃ A : MvPolynomial (Fin (d + 1)) ℂ,
      (∀ x, x ≠ 0 → MvPolynomial.eval x A = (Q x).coeff j) ∧
      ∀ x, ‖MvPolynomial.eval x A‖ ≤
        ((N.choose j : ℝ) * (max 1 C) ^ N) * (max 1 ‖x‖) ^ N :=
    PolynomialExtensionOf.Constructions.PolynomialExtension.exists_polynomial_of_punctured_growth
      (fun x hx => (hQc j).differentiableAt (isOpen_compl_singleton.mem_nhds hx)) (hb j)
  choose A hA hAb using hpoly
  exact ⟨Q, A, hA, fun x hx => ⟨hQm x hx, hQd x hx, hQr x hx⟩, hAb⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.PolynomialFiber.Constructions.PolynomialFiberCoefficients
