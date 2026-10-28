import OAI.RepresentationTheory.Hecke.RadialDilation.LocalCompactStabilization
import Mathlib.NumberTheory.Padics.ProperSpace

/-! # Local Bounded Stabilization -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.LocalBoundedStabilization.Realization

noncomputable section

/-! Entrywise bounded p-adic symplectic powers suffice for finite-order stabilization. -/

open scoped Classical _root_.Topology _root_.Matrix
open _root_.Matrix

variable (q n : ℕ) [Fact q.Prime]

theorem padicSymplectic_isClosed :
    IsClosed (Matrix.symplecticGroup (Fin n) ℚ_[q] : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ_[q])) := by
  let : T2Space (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ_[q]) :=
    inferInstanceAs (T2Space ((Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℚ_[q]))
  have h : IsClosed {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ_[q] |
      A.transpose * Matrix.J (Fin n) ℚ_[q] * A = Matrix.J (Fin n) ℚ_[q]} :=
    isClosed_eq (by fun_prop) continuous_const
  convert h using 1
  ext A
  exact SymplecticGroup.mem_iff'

theorem padicSymplectic_closedEmbedding :
    Topology.IsClosedEmbedding (fun g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n => g.val) :=
  (padicSymplectic_isClosed q n).isClosedEmbedding_subtypeVal

def localSymplecticBoundedSet (R : ℝ) : Set (Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n) :=
  {g | ∀ i j, ‖g.val i j‖ ≤ R}

theorem localSymplecticBoundedSet_isCompact (R : ℝ) : IsCompact (localSymplecticBoundedSet q n R) := by
  let C : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ_[q]) := {A | ∀ i j, ‖A i j‖ ≤ R}
  have hC : IsCompact C := by
    have hset : C = Set.pi Set.univ (fun _ : Fin n ⊕ Fin n =>
        Set.pi Set.univ (fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℚ_[q]) R)) := by
      ext A
      change (∀ i j, ‖A i j‖ ≤ R) ↔
        ∀ i ∈ (Set.univ : Set (Fin n ⊕ Fin n)),
          ∀ j ∈ (Set.univ : Set (Fin n ⊕ Fin n)), dist (A i j) 0 ≤ R
      simp only [Set.mem_univ, forall_const, dist_zero_right]
    rw [hset]
    exact isCompact_univ_pi (fun _ : Fin n ⊕ Fin n =>
      isCompact_univ_pi (fun _ : Fin n ⊕ Fin n => isCompact_closedBall (0 : ℚ_[q]) R))
  exact (padicSymplectic_closedEmbedding q n).isCompact_preimage hC

local instance c410LocalBoundedStabilization_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410LocalBoundedStabilization_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem exists_local_bounded_power_finite_phase
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n)
    (ψ : AddChar ℚ_[q] ℂ) (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hnontrivial : ∃ x, ψ x ≠ 1)
    (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) (R : ℝ)
    (hbounded : ∀ (N : ℕ) i j, ‖((Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g) ^ N).val i j‖ ≤ R) :
    ∃ (N : ℕ) (ξ : ℂ), 0 < N ∧ ξ ^ 8 = 1 ∧ Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ (g ^ N) f = ξ • f :=
  LocalCompactStabilization.Realization.exists_local_power_finite_phase q n hLocalWeil hn ψ hψ hunit hnontrivial g f
    (localSymplecticBoundedSet q n R) (localSymplecticBoundedSet_isCompact q n R) hbounded

end

end OAI.RepresentationTheory.Hecke.RadialDilation.LocalBoundedStabilization.Realization
