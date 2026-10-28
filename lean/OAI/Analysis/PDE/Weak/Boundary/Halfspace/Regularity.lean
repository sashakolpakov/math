import OAI.Analysis.PDE.Weak.Boundary.Halfspace.LocalNeighborhood
import OAI.Analysis.PDE.Weak.Boundary.NormalRegularity
import OAI.Analysis.PDE.Weak.Boundary.RegularityEntries
import OAI.Analysis.PDE.Weak.Boundary.Weak.Uniqueness
import OAI.Analysis.PDE.Weak.Elliptic.RegularSource

/-! Arbitrary finite-order boundary regularity for the genuine weak
zero-Dirichlet equation on a halfspace. -/

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem halfspace_regular_near_point
    (k : Fin (m + 1)) (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : SmoothBounded A)
    (hinv : SmoothBounded (fun x => (realOperatorEntry (A x) k k)⁻¹))
    {lam Λ D : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D)
    (hAM : ∀ x, ‖A x‖ ≤ Λ) (hDA : ∀ x, ‖fderiv ℝ A x‖ ≤ D)
    (hell : ∀ x z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (N : ℕ) {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    (p : H1Pair m) (hp : p ∈ H1Zero {x | 0 < x k})
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (hf : WeakRegularity ({x | 0 < x k} ∩ U) N f)
    (he : WeakDivergenceEquation ({x | 0 < x k} ∩ U) (fun x => A x (p.2 x)) f)
    {x₀ : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx₀ : x₀ ∈ U) :
    ∃ V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧
      WeakRegularity ({x | 0 < x k} ∩ V) (N + 1) p.2 := by
  let H : Set (OAI.Analysis.PDE.Variational.CellCoordinates m) := {x | 0 < x k}
  have hH : IsOpen H := isOpen_lt continuous_const (continuous_apply k)
  have hAm := fieldMultiplierCLM_ae (μ := volume) A hA.1.continuous.aestronglyMeasurable
    (Eventually.of_forall hAM)
  induction N generalizing U p f with
  | zero =>
    have hem := he.congr_ae (hAm p.2).symm Filter.EventuallyEq.rfl
    obtain ⟨V, hV, hxV, hVU, hder, _⟩ := local_halfspace_H2_near_point k A hA.1
      hlam hΛ hD hAM hDA hell p hp f hU hem x₀ hx₀
    refine ⟨V, hV, hxV, hVU, ?_⟩
    intro j
    obtain ⟨g, hg⟩ := hder j
    exact ⟨g, hg, trivial⟩
  | succ N ih =>
    obtain ⟨U₁, hU₁, hxU₁, hU₁U, hreg⟩ := ih hU p hp f hf.pred he hx₀
    have he₁ : WeakDivergenceEquation (H ∩ U₁) (fun x => A x (p.2 x)) f :=
      OAI.Analysis.PDE.Variational.weakEquation_congr_on he (inter_subset_inter_right H hU₁U)
        (Eventually.of_forall fun _ _ => rfl) (Eventually.of_forall fun _ _ => rfl)
    have hem := he₁.congr_ae (hAm p.2).symm Filter.EventuallyEq.rfl
    obtain ⟨U₂, hU₂, hxU₂, hU₂₁, _, htan⟩ := local_halfspace_H2_near_point k A hA.1
      hlam hΛ hD hAM hDA hell p hp f hU₁ hem x₀ hxU₁
    have h21 : H ∩ U₂ ⊆ H ∩ U₁ := inter_subset_inter_right H hU₂₁
    have h2U : H ∩ U₂ ⊆ H ∩ U := h21.trans (inter_subset_inter_right H hU₁U)
    have hchoices (j : Fin (m + 1)) : ∃ q : H1Pair m, q ∈ H1Zero H ∧
        (j ≠ k → HasWeakDirectionalDerivativeOn volume (H ∩ U₂) (Pi.single j 1) p.2 q.2) := by
      by_cases hj : j = k
      · exact ⟨p, hp, fun hn => False.elim (hn hj)⟩
      · obtain ⟨q, hq, _, hd⟩ := htan j hj
        exact ⟨q, hq, fun _ => hd⟩
    choose Q hQ hQg using hchoices
    have hbase : WeakRegularity (H ∩ U₁) (N + 1) p.2 := hreg
    choose Gd hGd hGreg using hreg
    have hGd₂ (j) := (hGd j).mono volume h21
    have hGreg₂ (j) := (hGreg j).mono_domain h21
    have he₂ : WeakDivergenceEquation (H ∩ U₂) (fun x => A x (p.2 x)) f :=
      OAI.Analysis.PDE.Variational.weakEquation_congr_on he h2U (Eventually.of_forall fun _ _ => rfl)
        (Eventually.of_forall fun _ _ => rfl)
    have hnext (j : Fin (m + 1)) : ∃ W : Set (OAI.Analysis.PDE.Variational.CellCoordinates m),
        IsOpen W ∧ x₀ ∈ W ∧ W ⊆ U₂ ∧
          (j ≠ k → WeakRegularity (H ∩ W) (N + 1) (Q j).2) := by
      by_cases hj : j = k
      · exact ⟨U₂, hU₂, hxU₂, subset_rfl, fun hn => False.elim (hn hj)⟩
      obtain ⟨fd, hfd, hfdreg⟩ := hf j
      obtain ⟨F, hF, heF⟩ := differentiated_equation_regular A hA p.2 Gd hGd₂
        (hbase.pred.mono_domain h21) hGreg₂ f fd (hfdreg.mono_domain h2U) j
        (hfd.mono volume h2U) he₂
      have heq := OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.vector_unique (hH.inter hU₂)
        (Lp.memLp (Gd j)) (Lp.memLp (Q j).2) (hGd₂ j) (hQg j hj)
      have heQ : WeakDivergenceEquation (H ∩ U₂) (fun x => A x ((Q j).2 x)) F := by
        apply OAI.Analysis.PDE.Variational.weakEquation_congr_on heF (subset_refl _)
        · filter_upwards [heq] with x hx
          exact fun hxs => congrArg (A x) (hx hxs).symm
        · exact Eventually.of_forall fun _ _ => rfl
      obtain ⟨W, hW, hxW, hWU₂, hWr⟩ := ih hU₂ (Q j) (hQ j) F hF heQ hxU₂
      exact ⟨W, hW, hxW, hWU₂, fun _ => hWr⟩
    choose W hW hxW hWU₂ hWr using hnext
    let V := U₂ ∩ ⋂ j, W j
    have hVU₂ : V ⊆ U₂ := inter_subset_left
    have hVW (j : Fin (m + 1)) : V ⊆ W j := fun x hx => mem_iInter.mp hx.2 j
    have hV : IsOpen V := hU₂.inter (isOpen_iInter_of_finite hW)
    have hxV : x₀ ∈ V := ⟨hxU₂, mem_iInter.mpr hxW⟩
    have hV₂ : H ∩ V ⊆ H ∩ U₂ := inter_subset_inter_right H hVU₂
    have hVU : V ⊆ U := hVU₂.trans (hU₂₁.trans hU₁U)
    have hder (j) (hj : j ≠ k) := (hQg j hj).mono volume hV₂
    have hregular (j) (hj : j ≠ k) :=
      (hWr j hj).mono_domain (inter_subset_inter_right H (hVW j))
    have heV : WeakDivergenceEquation (H ∩ V) (fun x => A x (p.2 x)) f :=
      OAI.Analysis.PDE.Variational.weakEquation_congr_on he (inter_subset_inter_right H hVU)
        (Eventually.of_forall fun _ _ => rfl) (Eventually.of_forall fun _ _ => rfl)
    obtain ⟨gn, hgn, hgnreg⟩ := OAI.Analysis.PDE.Weak.H1Zero.normal_gradient_regular (hH.inter hV) hp k (N + 1)
      (fun i j x => realOperatorEntry (A x) i j)
      (fun i j => smoothBounded_realOperatorEntry hA i j) hinv hlam
      (fun i j x => (realOperatorEntry_norm_le (A x) i j).trans (hAM x))
      (fun i j l x => (realOperatorEntry_derivative_norm_le A (hA.1.of_le (by simp)) i j l x).trans (hDA x))
      (fun x => realOperatorEntry_diagonal_lower (A x) (hell x) k)
      (fun x => A x (p.2 x))
      (fieldMultiplier_memLp A hA.1.continuous.aestronglyMeasurable (Eventually.of_forall hAM) p.2)
      (fun x i => realOperatorEntry_apply (A x) (p.2 x) i) f (Lp.memLp f) heV
      (fun j => (Q j).2) (fun j => Lp.memLp (Q j).2) hder
      ((hbase.mono_domain (hV₂.trans h21)).function)
      ((hf.mono_domain (inter_subset_inter_right H hVU)).function)
      (fun j hj => (hregular j hj).function)
    refine ⟨V, hV, hxV, hVU, ?_⟩
    intro j
    by_cases hj : j = k
    · subst j
      exact ⟨gn, hgn, hgnreg⟩
    · exact ⟨(Q j).2, hder j hj, hregular j hj⟩

end OAI.Analysis.PDE.Weak
