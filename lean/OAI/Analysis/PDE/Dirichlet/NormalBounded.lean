import OAI.Analysis.PDE.Dirichlet.NormalCompact
import Mathlib.Analysis.Matrix.Normed

open Set Metric
open scoped Matrix ComplexOrder MatrixOrder Topology Matrix.Norms.Elementwise

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

def quaternionTangentProjection {n : ℕ} (ν z : Fin n → Q) : Fin n → Q :=
  fun i ↦ z i - ν i * quaternionPairing ν z

theorem quaternionTangentProjection_tangent {n : ℕ} (ν z : Fin n → Q)
    (hν : quaternionPairing ν ν = 1) :
    quaternionPairing ν (quaternionTangentProjection ν z) = 0 := by
  simp only [quaternionTangentProjection, quaternionPairing, mul_sub,
    Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul]
  change quaternionPairing ν z - quaternionPairing ν ν * quaternionPairing ν z = 0
  rw [hν, one_mul, sub_self]

theorem quaternionTangentProjection_of_tangent {n : ℕ} (ν z : Fin n → Q)
    (h : quaternionPairing ν z = 0) : quaternionTangentProjection ν z = z := by
  funext i
  simp [quaternionTangentProjection, h]

theorem continuous_quaternionPairing {X : Type*} [TopologicalSpace X] {n : ℕ}
    {u v : X → Fin n → Q} (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun x ↦ quaternionPairing (u x) (v x)) := by
  unfold quaternionPairing
  fun_prop

theorem continuous_quaternionForm_re {X : Type*} [TopologicalSpace X] {n : ℕ}
    {A : X → Matrix (Fin n) (Fin n) Q} {z : X → Fin n → Q}
    (hA : Continuous A) (hz : Continuous z) :
    Continuous (fun x ↦ (quaternionForm (A x) (z x)).re) := by
  apply Quaternion.continuous_re.comp
  unfold quaternionForm
  fun_prop

theorem continuous_quaternionTangentProjection {X : Type*} [TopologicalSpace X] {n : ℕ}
    {ν z : X → Fin n → Q} (hν : Continuous ν) (hz : Continuous z) :
    Continuous (fun x ↦ quaternionTangentProjection (ν x) (z x)) := by
  have hp := continuous_quaternionPairing hν hz
  unfold quaternionTangentProjection
  fun_prop

def boundedNormalData (n : ℕ) (K L c : ℝ) :
    Set (Matrix (Fin (n + 1)) (Fin (n + 1)) Q × (Fin (n + 1) → Q)) :=
  {p | ‖p.1‖ ≤ K ∧ ‖p.2‖ ≤ L ∧ p.1.IsHermitian ∧ quaternionPairing p.2 p.2 = 1 ∧
    ∀ z, c * (quaternionForm 1 (quaternionTangentProjection p.2 z)).re ≤
      (quaternionForm p.1 (quaternionTangentProjection p.2 z)).re}

theorem isCompact_boundedNormalData (n : ℕ) (K L c : ℝ) :
    IsCompact (boundedNormalData n K L c) := by
  apply ((isCompact_closedBall (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q) K).prod
    (isCompact_closedBall (0 : Fin (n + 1) → Q) L)).of_isClosed_subset
  · refine (isClosed_le continuous_fst.norm continuous_const).inter
      ((isClosed_le continuous_snd.norm continuous_const).inter (?_ : IsClosed {p :
        Matrix (Fin (n + 1)) (Fin (n + 1)) Q × (Fin (n + 1) → Q) |
        p.1.IsHermitian ∧ quaternionPairing p.2 p.2 = 1 ∧
          ∀ z, c * (quaternionForm 1 (quaternionTangentProjection p.2 z)).re ≤
            (quaternionForm p.1 (quaternionTangentProjection p.2 z)).re}))
    refine (isClosed_eq (by fun_prop) continuous_fst).inter
      ((isClosed_eq (continuous_quaternionPairing continuous_snd continuous_snd) continuous_const).inter ?_)
    have hf : ∀ z : Fin (n + 1) → Q, IsClosed {p :
        Matrix (Fin (n + 1)) (Fin (n + 1)) Q × (Fin (n + 1) → Q) |
        c * (quaternionForm 1 (quaternionTangentProjection p.2 z)).re ≤
          (quaternionForm p.1 (quaternionTangentProjection p.2 z)).re} := by
      intro z
      have hp : Continuous (fun p : Matrix (Fin (n + 1)) (Fin (n + 1)) Q × (Fin (n + 1) → Q) ↦
          quaternionTangentProjection p.2 z) :=
        continuous_quaternionTangentProjection continuous_snd continuous_const
      exact isClosed_le (continuous_const.mul (continuous_quaternionForm_re continuous_const hp))
        (continuous_quaternionForm_re continuous_fst hp)
    have heq : (⋂ z : Fin (n + 1) → Q, {p :
        Matrix (Fin (n + 1)) (Fin (n + 1)) Q × (Fin (n + 1) → Q) |
        c * (quaternionForm 1 (quaternionTangentProjection p.2 z)).re ≤
          (quaternionForm p.1 (quaternionTangentProjection p.2 z)).re}) =
        (fun p ↦ ∀ z, c * (quaternionForm 1 (quaternionTangentProjection p.2 z)).re ≤
          (quaternionForm p.1 (quaternionTangentProjection p.2 z)).re) := by
      ext p
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      rfl
    exact heq ▸ isClosed_iInter hf
  · intro p hp
    exact ⟨by simpa using hp.1, by simpa using hp.2.1⟩

/-- Bounded tangential data and a uniformly positive tangential restriction
give a uniform bound for the unknown normal coefficient of the Hessian. -/
theorem normal_parameter_bound_of_bounded_data (n : ℕ) (K L c F : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Q)
      (ν : Fin (n + 1) → Q) (a : ℝ),
      ‖A‖ ≤ K → ‖ν‖ ≤ L → A.IsHermitian → quaternionPairing ν ν = 1 →
      (∀ z, quaternionPairing ν z = 0 → c * (quaternionForm 1 z).re ≤ (quaternionForm A z).re) →
      |OAI.LinearAlgebra.Moore.mooreDet (n + 1) (A + a • OAI.Analysis.Calculus.Quaternion.outer ν)| ≤ F → |a| ≤ C := by
  have hpos : ∀ p ∈ boundedNormalData n K L c, ∀ z : Fin (n + 1) → Q,
      z ≠ 0 → quaternionPairing p.2 z = 0 → 0 < (quaternionForm p.1 z).re := by
    intro p hp z hz ht
    have h := hp.2.2.2.2 z
    rw [quaternionTangentProjection_of_tangent _ _ ht] at h
    have hi : (OAI.LinearAlgebra.Moore.complexify (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q)).PosDef := by
      rw [OAI.LinearAlgebra.Moore.complexify_one]
      exact Matrix.PosDef.one
    have hzpos := (OAI.LinearAlgebra.Moore.complexify_posDef_iff Matrix.isHermitian_one).mp hi z hz
    exact (mul_pos hc hzpos).trans_le h
  obtain ⟨C, hC, hbound⟩ := normal_parameter_bound_on_compact
    (isCompact_boundedNormalData n K L c) continuous_fst continuous_snd
    (fun p hp ↦ hp.2.2.1) (fun p hp ↦ hp.2.2.2.1) hpos F
  refine ⟨C, hC, ?_⟩
  intro A ν a hA hν hAH hunit ht hdet
  apply hbound (A, ν) ?_ a hdet
  refine ⟨hA, hν, hAH, hunit, ?_⟩
  intro z
  exact ht _ (quaternionTangentProjection_tangent ν z hunit)

end OAI.Analysis.PDE.Dirichlet
