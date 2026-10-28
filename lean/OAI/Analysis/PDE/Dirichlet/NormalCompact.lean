import OAI.Analysis.PDE.Dirichlet.NormalCoefficient
import OAI.Analysis.PDE.Dirichlet.Continuity

open Set
open scoped Matrix ComplexOrder MatrixOrder Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem continuous_outer_map {X : Type*} [TopologicalSpace X] {n : ℕ}
    {ν : X → Fin n → Q} (hν : Continuous ν) : Continuous (fun x ↦ OAI.Analysis.Calculus.Quaternion.outer (ν x)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((continuous_apply i).comp hν).mul (((continuous_apply j).comp hν).star)

/-- On a compact family with positive tangential blocks, the determinant
equation uniformly bounds its one remaining normal rank-one parameter. -/
theorem normal_parameter_bound_on_compact {X : Type*} [TopologicalSpace X] {n : ℕ}
    {S : Set X} (hS : IsCompact S)
    {A : X → Matrix (Fin (n + 1)) (Fin (n + 1)) Q} {ν : X → Fin (n + 1) → Q}
    (hA : Continuous A) (hν : Continuous ν)
    (hAH : ∀ x ∈ S, (A x).IsHermitian)
    (hunit : ∀ x ∈ S, quaternionPairing (ν x) (ν x) = 1)
    (ht : ∀ x ∈ S, ∀ z : Fin (n + 1) → Q, z ≠ 0 → quaternionPairing (ν x) z = 0 →
      0 < (quaternionForm (A x) z).re) (F : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ S, ∀ a : ℝ,
      |OAI.LinearAlgebra.Moore.mooreDet (n + 1) (A x + a • OAI.Analysis.Calculus.Quaternion.outer (ν x))| ≤ F → |a| ≤ C := by
  by_cases hne : S.Nonempty
  · let c : X → ℝ := fun x ↦ OAI.LinearAlgebra.Moore.mooreDifferential (n + 1) (A x) (OAI.Analysis.Calculus.Quaternion.outer (ν x))
    have hp : Continuous (fun x ↦ (A x, OAI.Analysis.Calculus.Quaternion.outer (ν x))) :=
      hA.prodMk (continuous_outer_map hν)
    have hc : Continuous c := (OAI.LinearAlgebra.Moore.continuous_mooreDifferential (n + 1)).comp
      (f := fun x ↦ (A x, OAI.Analysis.Calculus.Quaternion.outer (ν x))) hp
    have hcpos : ∀ x ∈ S, 0 < c x := fun x hx ↦
      moore_normal_coefficient_pos (A x) (hAH x hx) (ν x) (hunit x hx) (ht x hx)
    obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn hne hc.continuousOn
    have hc₀ : 0 < c x₀ := hcpos x₀ hx₀
    obtain ⟨K, hK⟩ := hS.bddAbove_image (((OAI.LinearAlgebra.Moore.continuous_mooreDet (n + 1)).comp hA).abs.continuousOn)
    let C := (|F| + max K 0 + 1) / c x₀
    have hC : 0 < C := div_pos (by positivity) hc₀
    refine ⟨C, hC, ?_⟩
    intro x hx a hdet
    have hkx : |OAI.LinearAlgebra.Moore.mooreDet (n + 1) (A x)| ≤ max K 0 :=
      (hK (mem_image_of_mem _ hx)).trans (le_max_left _ _)
    have hcx : c x₀ ≤ c x := hmin hx
    have heq : a * c x = OAI.LinearAlgebra.Moore.mooreDet (n + 1) (A x + a • OAI.Analysis.Calculus.Quaternion.outer (ν x)) - OAI.LinearAlgebra.Moore.mooreDet (n + 1) (A x) := by
      rw [OAI.LinearAlgebra.Moore.mooreDet_add_outer_differential]
      dsimp only [c]
      ring
    have hprod : |a| * c x ≤ |F| + max K 0 := by
      calc
        _ = |a * c x| := by rw [abs_mul, abs_of_pos (hcpos x hx)]
        _ = |OAI.LinearAlgebra.Moore.mooreDet (n + 1) (A x + a • OAI.Analysis.Calculus.Quaternion.outer (ν x)) - OAI.LinearAlgebra.Moore.mooreDet (n + 1) (A x)| := congrArg abs heq
        _ ≤ |OAI.LinearAlgebra.Moore.mooreDet (n + 1) (A x + a • OAI.Analysis.Calculus.Quaternion.outer (ν x))| + |OAI.LinearAlgebra.Moore.mooreDet (n + 1) (A x)| := abs_sub _ _
        _ ≤ |F| + max K 0 := add_le_add (hdet.trans (le_abs_self F)) hkx
    apply (le_div_iff₀ hc₀).mpr
    exact (mul_le_mul_of_nonneg_left hcx (abs_nonneg a)).trans (hprod.trans (by linarith))
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

end OAI.Analysis.PDE.Dirichlet
