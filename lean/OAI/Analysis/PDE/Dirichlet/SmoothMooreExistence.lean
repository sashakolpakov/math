import OAI.Analysis.PDE.Dirichlet.SmoothMooreSolver
import OAI.Analysis.PDE.Dirichlet.Periodic.CoefficientMooreSmooth

open Set Module InnerProductSpace
open scoped ContDiff Topology Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
  [Fintype ι]

omit [FiniteDimensional ℝ P] in
/-- Smooth-data solvability for the actual Moore linearization on a
periodic domain. The coordinate chart, compact transverse box, coefficient
regularity, ellipticity neighborhood, and variational solution are all
constructed. No inverse or linear solvability hypothesis is assumed. -/
theorem exists_smooth_moore_dirichlet_solution
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C)
    {r ψ g : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hψ : ContDiff ℝ ∞ ψ) (hψp : LatticePeriodic e lat ψ)
    (hpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (hg : ContDiff ℝ ∞ g) (hgp : LatticePeriodic e lat g)
    (q : ℕ) (hq : 2 ≤ q) :
    ∃ u : CoordinateSpace n 4 → ℝ, ContDiff ℝ q u ∧ LatticePeriodic e lat u ∧
      (∀ x, r x = 0 → u x = 0) ∧
      (∀ x, r x < 0 → mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) u x = g x) := by
  classical
  let N := finrank ℝ V
  have hN : 0 < N := Module.finrank_pos (R := ℝ) (M := V)
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let c : Basis (Fin N) ℝ V := Module.finBasis ℝ V
  let m := Fintype.card ι + N - 1
  have hcard : Fintype.card (Fin (m + 1)) = Fintype.card (ι ⊕ Fin N) := by
    simp only [Fintype.card_fin, Fintype.card_sum]
    dsimp [m]
    omega
  let d : Fin (m + 1) ≃ ι ⊕ Fin N := Fintype.equivOfCardEq hcard
  obtain ⟨U, lam, hU, hDU, hlam, hell⟩ :=
    smooth_mooreCoefficient_elliptic_neighborhood hn e lat hC hr.continuous hrp hbounded
      hψ hψp hpos
  apply exists_smooth_moore_dirichlet_solution_of_elliptic e lat c d hC
    hr hrp hbounded hreg hψ hψp hg hgp (contDiff_smooth_mooreCoefficient hψ)
    hU hDU hlam ?_ q hq
  intro x hx z
  simpa only [real_inner_comm] using hell x hx z

end OAI.Analysis.PDE.Dirichlet
