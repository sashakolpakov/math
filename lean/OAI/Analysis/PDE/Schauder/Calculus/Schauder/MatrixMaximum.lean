import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MaximumInfinity
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Normalization

/-! Maximum principles for genuine pointwise positive-definite matrix coefficients. -/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet

theorem matrix_directional_representation {m : ℕ} (hm : 0 < m)
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ x, (A x).PosDef) :
    ∃ v : EuclideanSpace ℝ (Fin m) → Fin m → EuclideanSpace ℝ (Fin m),
      (∀ x, 0 < ∑ i, ‖v x i‖ ^ 2) ∧
      (∀ f x, OAI.Analysis.PDE.Dirichlet.ellipticValue (fun _ _ => 1) v f x = nondivergenceOperator A f x) := by
  choose L hL hn using fun x => exists_elliptic_normalization (A x) (hA x)
  refine ⟨fun x i => L x (EuclideanSpace.single i 1), ?_, ?_⟩
  · intro x
    apply Finset.sum_pos'
    · intro i _
      positivity
    · refine ⟨⟨0, hm⟩, Finset.mem_univ _, ?_⟩
      apply sq_pos_of_pos
      apply norm_pos_iff.mpr
      intro hz
      have he : EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ) = 0 :=
        (L x).injective (hz.trans (map_zero (L x)).symm)
      have hc := congrArg (fun z : EuclideanSpace ℝ (Fin m) => z ⟨0, hm⟩) he
      simp at hc
  · intro f x
    simp only [OAI.Analysis.PDE.Dirichlet.ellipticValue, one_mul]
    rw [bilinear_trace_pullback]
    change (∑ i : Fin m, ∑ j : Fin m, linearEllipticMatrix (L x).toContinuousLinearMap i j *
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = _
    rw [hL x]
    rfl

theorem matrix_maximum_principle_at_infinity {m : ℕ} (hm : 0 < m)
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ x, (A x).PosDef) (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContDiff ℝ 2 f) (hL : ∀ x, 0 ≤ nondivergenceOperator A f x)
    (hf0 : Tendsto f (cocompact _) (𝓝 0)) (x : EuclideanSpace ℝ (Fin m)) : f x ≤ 0 := by
  obtain ⟨v, hv, he⟩ := matrix_directional_representation hm A hA
  apply maximum_principle_at_infinity (fun _ _ => 1) v f hf (by intros; norm_num) ?_ ?_ hf0 x
  · simpa only [one_mul] using hv
  · intro y
    rw [he]
    exact hL y

theorem matrix_uniqueness_at_infinity {m : ℕ} (hm : 0 < m)
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ x, (A x).PosDef) (f g : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hL : ∀ x, nondivergenceOperator A f x = nondivergenceOperator A g x)
    (hf0 : Tendsto f (cocompact _) (𝓝 0)) (hg0 : Tendsto g (cocompact _) (𝓝 0)) : f = g := by
  obtain ⟨v, hv, he⟩ := matrix_directional_representation hm A hA
  apply uniqueness_at_infinity (fun _ _ => 1) v f g hf hg (by intros; norm_num) ?_ ?_ hf0 hg0
  · simpa only [one_mul] using hv
  · intro x
    rw [he, he]
    exact hL x

end OAI.Analysis.PDE.Schauder
