import OAI.Analysis.HodgeTheory.Decomposition.GraphMultiplier
import OAI.Analysis.HodgeTheory.Decomposition.RellichCover
import OAI.Analysis.HodgeTheory.Decomposition.Multiplier

/-! # Smooth Global -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SmoothGlobal.Constructions

noncomputable section

section

/-! Global Rellich compactness for genuine smooth forms bounded in the
actual Hodge graph norm, using a finite smooth real partition of unity. -/

open Set
open scoped _root_.Manifold ContDiff BigOperators

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem projective_real_partition_forms_sum {ι : Type*} [Fintype ι] (n : ℕ)
    (f : ι → V.analyticSpace → ℝ)
    (hf : ∀ i, ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ (f i))
    (hsum : ∀ x, ∑ i, f i x = 1)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    (∑ i, RealMultiplier.Constructions.projectiveRealMultiplier V n (f i) (hf i) a) = a := by
  apply DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  change DifferentialForms.Manifold.Algebra.SmoothManifoldForm.eval x (∑ i, RealMultiplier.Constructions.projectiveRealMultiplier V n (f i) (hf i) a) = a x
  rw [map_sum]
  change (∑ i, (f i x : ℂ) • a x) = a x
  rw [← Finset.sum_smul]
  have hsumC : (∑ i, (f i x : ℂ)) = 1 := by exact_mod_cast hsum x
  rw [hsumC, one_smul]

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

theorem projectiveSmooth_graph_ball_rellich (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (closure ((Form.Constructions.smoothToProjectiveL2 V (n + 1)) ''
      {a | ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ ≤ R})) := by
  classical
  obtain ⟨s, U, hU, hcover, hUsource, hrellich⟩ := RellichCover.Constructions.exists_projective_finite_rellich_cover V n
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, V.analyticModel)) isClosed_univ U hU
    (fun x _ => mem_iUnion.mpr (hcover x))
  have hρsmooth (i : s) : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ (ρ i) := (ρ i).contMDiff
  have hρsum (x : V.analyticSpace) : ∑ i : s, ρ i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  have hρsource (i : s) : tsupport (ρ i) ⊆ (chartAt V.analyticModel i.val).source := (hρ i).trans (hUsource i)
  choose B hB hmul using (fun i : s => GraphMultiplier.Constructions.projectiveRealMultiplier_graph_bound V
    (chartAt V.analyticModel i.val) (chart_mem_atlas _ _) n (ρ i) (hρsmooth i) (hρsource i))
  let T := fun i : s => closure ((Form.Constructions.smoothToProjectiveL2 V (n + 1)) ''
    {a | (∀ x, x ∉ tsupport (ρ i) → a x = 0) ∧ ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ ≤ B i * R})
  have hT (i : s) : IsCompact (T i) := hrellich i (tsupport (ρ i)) (isClosed_tsupport _).isCompact
    (hρ i) (B i * R) (mul_nonneg (hB i) hR)
  have hP : IsCompact {u : s → Form.Constructions.ProjectiveL2Forms V (n + 1) | ∀ i, u i ∈ T i} := isCompact_pi_infinite hT
  have hcont : Continuous (fun u : s → Form.Constructions.ProjectiveL2Forms V (n + 1) => ∑ i, u i) :=
    continuous_finsetSum _ (fun i _ => continuous_apply i)
  have hcompact := hP.image hcont
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hcompact.isClosed
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨fun i => Form.Constructions.smoothToProjectiveL2 V (n + 1) (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) (ρ i) (hρsmooth i) a), ?_, ?_⟩
  · intro i
    apply subset_closure
    refine ⟨RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) (ρ i) (hρsmooth i) a, ⟨?_, ?_⟩, rfl⟩
    · exact fun _ hx => RealMultiplier.Constructions.projectiveRealMultiplier_zero_off_support V (n + 1) (ρ i) (hρsmooth i) a hx
    · exact (hmul i a).trans (mul_le_mul_of_nonneg_left ha (hB i))
  · dsimp only
    rw [← map_sum, projective_real_partition_forms_sum V (n + 1) (fun i => ρ i) hρsmooth hρsum a]

end

section

/-! Genuine L² cutoff multipliers absorb locally trivial outer cutoffs,
and a finite real partition of unity sums to the identity on completed L². -/

open scoped ContDiff _root_.Manifold

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

def projectiveRealL2Multiplier (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f) :
    Form.Constructions.ProjectiveL2Forms V n →L[ℂ] Form.Constructions.ProjectiveL2Forms V n :=
  Multiplier.Constructions.projectiveL2Multiplier V n (fun x => (f x : ℂ)) (RealMultiplier.Constructions.projectiveRealFunction_complex_smooth V f hf)

theorem projectiveRealL2Multiplier_on_smooth (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    projectiveRealL2Multiplier V n f hf (Form.Constructions.smoothToProjectiveL2 V n a) =
      Form.Constructions.smoothToProjectiveL2 V n (RealMultiplier.Constructions.projectiveRealMultiplier V n f hf a) :=
  Multiplier.Constructions.projectiveL2Multiplier_on_smooth V n _ _ a

theorem projectiveL2Multiplier_absorb (f g : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (hfg : ∀ x ∈ tsupport f, g x = 1) (u : Form.Constructions.ProjectiveL2Forms V n) :
    Multiplier.Constructions.projectiveL2Multiplier V n f hf (Multiplier.Constructions.projectiveL2Multiplier V n g hg u) = Multiplier.Constructions.projectiveL2Multiplier V n f hf u := by
  have hclosed : IsClosed {v : Form.Constructions.ProjectiveL2Forms V n |
      Multiplier.Constructions.projectiveL2Multiplier V n f hf (Multiplier.Constructions.projectiveL2Multiplier V n g hg v) = Multiplier.Constructions.projectiveL2Multiplier V n f hf v} :=
    isClosed_eq ((Multiplier.Constructions.projectiveL2Multiplier V n f hf).continuous.comp (Multiplier.Constructions.projectiveL2Multiplier V n g hg).continuous)
      (Multiplier.Constructions.projectiveL2Multiplier V n f hf).continuous
  refine (Form.Constructions.smoothToProjectiveL2_dense V n).induction_on u hclosed (fun a => ?_)
  change Multiplier.Constructions.projectiveL2Multiplier V n f hf (Multiplier.Constructions.projectiveL2Multiplier V n g hg (Form.Constructions.smoothToProjectiveL2 V n a)) = _
  rw [Multiplier.Constructions.projectiveL2Multiplier_on_smooth, Multiplier.Constructions.projectiveL2Multiplier_on_smooth, Multiplier.Constructions.projectiveL2Multiplier_on_smooth]
  apply congrArg (Form.Constructions.smoothToProjectiveL2 V n)
  apply DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  change f x • (g x • a x) = f x • a x
  by_cases hx : x ∈ tsupport f
  · rw [hfg x hx, one_smul]
  · rw [image_eq_zero_of_notMem_tsupport hx]
    ext v
    simp

theorem projectiveRealL2Multiplier_partition {ι : Type*} [Fintype ι]
    (f : ι → V.analyticSpace → ℝ)
    (hf : ∀ i, ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ (f i))
    (hsum : ∀ x, ∑ i, f i x = 1) (u : Form.Constructions.ProjectiveL2Forms V n) :
    (∑ i, projectiveRealL2Multiplier V n (f i) (hf i) u) = u := by
  have hclosed : IsClosed {v : Form.Constructions.ProjectiveL2Forms V n | (∑ i, projectiveRealL2Multiplier V n (f i) (hf i) v) = v} :=
    isClosed_eq (continuous_finsetSum _ (fun i _ => (projectiveRealL2Multiplier V n (f i) (hf i)).continuous))
      continuous_id
  refine (Form.Constructions.smoothToProjectiveL2_dense V n).induction_on u hclosed (fun a => ?_)
  change (∑ i, projectiveRealL2Multiplier V n (f i) (hf i) (Form.Constructions.smoothToProjectiveL2 V n a)) = _
  simp only [projectiveRealL2Multiplier_on_smooth]
  rw [← map_sum, projective_real_partition_forms_sum V n f hf hsum a]

end

/-! Genuine smooth representatives of all sufficiently small cutoffs of
one completed L² form assemble into a global smooth representative. -/

open Set
open scoped _root_.Manifold ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

theorem projective_smooth_representative_of_local_cutoffs
    (u : Form.Constructions.ProjectiveL2Forms V n)
    (hlocal : ∀ x : V.analyticSpace, ∃ U : Set V.analyticSpace, IsOpen U ∧ x ∈ U ∧
      ∀ ρ : V.analyticSpace → ℝ, ∀ hρ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ ρ,
        tsupport ρ ⊆ U → ∃ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n,
          Form.Constructions.smoothToProjectiveL2 V n a = projectiveRealL2Multiplier V n ρ hρ u) :
    ∃ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n, Form.Constructions.smoothToProjectiveL2 V n a = u := by
  classical
  choose U hU hxU hrepr using hlocal
  obtain ⟨s, hcover⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  have hscover : ∀ x : V.analyticSpace, ∃ i : s, x ∈ U i.val := by
    intro x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
    exact ⟨⟨y, hy⟩, hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, V.analyticModel)) isClosed_univ (fun i : s => U i.val) (fun i => hU i.val)
    (fun x _ => mem_iUnion.mpr (hscover x))
  have hρsmooth (i : s) : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ (ρ i) := (ρ i).contMDiff
  have hρsum (x : V.analyticSpace) : ∑ i : s, ρ i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  choose a ha using (fun i : s => hrepr i.val (ρ i) (hρsmooth i) (hρ i))
  refine ⟨∑ i : s, a i, ?_⟩
  rw [map_sum]
  simp only [ha]
  exact projectiveRealL2Multiplier_partition V n (fun i : s => ρ i) hρsmooth hρsum u

end

end OAI.Analysis.HodgeTheory.Decomposition.SmoothGlobal.Constructions
