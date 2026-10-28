import OAI.Geometry.ComplexTorus.RiemannProjectivity.CoefficientRoot
import OAI.Geometry.ComplexTorus.RiemannProjectivity.RemovableGlobal
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericDegree

/-! # Bounded Polynomial -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.BoundedPolynomial.Constructions.BoundedPolynomialExtension

noncomputable section

/-!
# RiemannProjectivity: extending bounded-root monic families through an exceptional hypersurface

The lower coefficients have uniform bounds from the roots, including their
multiplicities. Scalar removability extends each of the finitely many
coefficients; their common neighborhood carries a monic polynomial family.
-/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem exists_extension {Q : V → ℂ[X]} {c : V → ℂ} {O : Set V}
    (hO : IsOpen O) (hc : DifferentiableOn ℂ c O) {x : V} (hx : x ∈ O)
    (hn : ¬∀ᶠ y in 𝓝 x, c y = 0) (k : ℕ)
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (Q y).coeff j) (O ∩ {y | c y ≠ 0}))
    (hmonic : ∀ y ∈ O, c y ≠ 0 → (Q y).Monic ∧ (Q y).natDegree = k)
    {R : ℝ} (hroot : ∀ y ∈ O, c y ≠ 0 → ∀ z, (Q y).eval z = 0 → ‖z‖ ≤ R) :
    ∃ (P : V → ℂ[X]) (U : Set V), IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧
      (∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) U) ∧
      (∀ y, (P y).Monic ∧ (P y).natDegree = k) ∧
      ∀ y ∈ U, c y ≠ 0 → P y = Q y := by
  classical
  have hlocal (j : ℕ) : ∃ (U : Set V) (H : V → ℂ), IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧
      DifferentiableOn ℂ H U ∧ EqOn H (fun y => (Q y).coeff j) (U ∩ {y | c y ≠ 0}) := by
    have hb (y : V) (hy : y ∈ O ∩ {y | c y ≠ 0}) :
        ‖(Q y).coeff j‖ ≤ (k.choose j : ℝ) * (max 1 R) ^ k := by
      have h := CoefficientRoot.Constructions.RootCoefficientBound.norm_coeff_le (hmonic y hy.1 hy.2).1
        (hroot y hy.1 hy.2) j
      simpa only [(hmonic y hy.1 hy.2).2] using h
    obtain ⟨U, H, hU, hxU, hUO, hH, heq, _⟩ :=
      RemovableGlobal.Constructions.RemovableHypersurface.exists_local_bounded_extension hO hc (hcoeff j) hx hn hb
    exact ⟨U, H, hU, hxU, hUO, hH, heq⟩
  choose U H hU hxU hUO hH heq using hlocal
  let W : Set V := O ∩ ⋂ j : Fin k, U j.val
  have hWO : W ⊆ O := inter_subset_left
  have hWj (j : ℕ) (hj : j < k) : W ⊆ U j := by
    intro y hy
    exact mem_iInter.mp hy.2 ⟨j, hj⟩
  let P : V → ℂ[X] := fun y => CoefficientRoot.Constructions.MonicFamily.ofCoefficients k (fun j => H j y)
  refine ⟨P, W, hO.inter (isOpen_iInter_of_finite (fun j => hU j.val)),
    ⟨hx, mem_iInter.mpr (fun j => hxU j.val)⟩, hWO, ?_, ?_, ?_⟩
  · intro j
    change DifferentiableOn ℂ (fun y => (CoefficientRoot.Constructions.MonicFamily.ofCoefficients k (fun i => H i y)).coeff j) W
    simp only [CoefficientRoot.Constructions.MonicFamily.coeff_ofCoefficients]
    by_cases hj : j < k
    · simp only [hj, ite_true]
      exact (differentiableOn_const _).add ((hH j).mono (hWj j hj))
    · simp only [hj, ite_false, add_zero]
      exact differentiableOn_const _
  · intro y
    exact CoefficientRoot.Constructions.MonicFamily.monic_ofCoefficients k _
  · intro y hy hcy
    exact CoefficientRoot.Constructions.MonicFamily.ofCoefficients_eq (hmonic y (hWO hy) hcy).1
      (hmonic y (hWO hy) hcy).2 (fun j hj => heq j ⟨hWj j hj hy, hcy⟩)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.BoundedPolynomial.Constructions.BoundedPolynomialExtension
