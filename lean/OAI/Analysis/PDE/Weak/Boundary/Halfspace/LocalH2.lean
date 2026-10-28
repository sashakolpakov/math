import OAI.Analysis.PDE.Weak.Boundary.NormalVector
import OAI.Analysis.PDE.Weak.Boundary.OperatorEntries
import OAI.Analysis.PDE.Weak.Boundary.TangentialLocalH2

/-! Local H² regularity right up to a flat zero-Dirichlet boundary.
Tangential derivatives come from the boundary difference quotient estimate;
the normal derivative is recovered from the equation. -/

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem local_halfspace_gradient_weak_derivatives_on_plateau
    (k : Fin (m + 1)) (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {lam Λ D K L : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hAM : ∀ x, ‖A x‖ ≤ Λ) (hDA : ∀ x, ‖fderiv ℝ A x‖ ≤ D)
    (hell : ∀ x z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero {x | 0 < x k})
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    (hweak : WeakDivergenceEquation ({x | 0 < x k} ∩ U)
      (fieldMultiplierCLM A hA.continuous.aestronglyMeasurable (Eventually.of_forall hAM) p.2) f)
    (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η) (hs : HasCompactSupport η)
    (hsub : tsupport η ⊆ U)
    (hηM : ∀ x, |η x| ≤ 1) (hηK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K)
    (hηL : ∀ x, ‖fderiv ℝ η x‖ ≤ L)
    {V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hV : IsOpen V) (hone : ∀ x ∈ V, η x = 1) (hVU : V ⊆ U) :
    ∀ j : Fin (m + 1), ∃ g : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)),
      HasWeakDirectionalDerivativeOn volume ({x | 0 < x k} ∩ V) (Pi.single j 1) p.2 g := by
  let ℓ : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ := ContinuousLinearMap.proj k
  have htan : ∀ j, ∃ g : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)),
      j ≠ k → HasWeakDirectionalDerivative volume (Pi.single j 1)
        (cutoffL2 η hη.continuous hηM p.2) g := by
    intro j
    by_cases hj : j = k
    · exact ⟨0, fun h => False.elim (h hj)⟩
    · obtain ⟨g, _, hg⟩ := local_halfspace_tangential_weak_gradient_derivative ℓ A (hA.of_le (by simp))
        hlam hΛ hD hK hAM hDA hell p hp f hU hweak η hη hs hsub hηM hηK hηL j
        (by simp [ℓ, Ne.symm hj])
      exact ⟨g, fun _ => hg⟩
  choose g hg using htan
  let Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m) := {x | 0 < x k} ∩ V
  have hΩ : IsOpen Ω := (isOpen_lt continuous_const (continuous_apply k)).inter hV
  have hder (j) (hj : j ≠ k) : HasWeakDirectionalDerivativeOn volume Ω (Pi.single j 1) p.2 (g j) :=
    (hg j hj).cutoff_eq_one volume hη.continuous hηM (fun x hx => hone x hx.2)
  let H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m := fun x => A x (p.2 x)
  have hH : MemLp H 2 volume :=
    fieldMultiplier_memLp A hA.continuous.aestronglyMeasurable (Eventually.of_forall hAM) p.2
  have hweakH : WeakDivergenceEquation Ω H f := by
    have he := hweak.congr_ae
      (fieldMultiplierCLM_ae A hA.continuous.aestronglyMeasurable (Eventually.of_forall hAM) p.2)
      Filter.EventuallyEq.rfl
    exact fun φ hφ hs hsub => he φ hφ hs (fun x hx => ⟨(hsub hx).1, hVU (hsub hx).2⟩)
  obtain ⟨G, hG, hGD⟩ := OAI.Analysis.PDE.Weak.H1Zero.normal_gradient_derivative hΩ hp k
    (fun i j x => realOperatorEntry (A x) i j)
    (fun i j => contDiff_realOperatorEntry A hA i j) hlam
    (fun i j x => (realOperatorEntry_norm_le (A x) i j).trans (hAM x))
    (fun i j l x => (realOperatorEntry_derivative_norm_le A (hA.of_le (by simp)) i j l x).trans (hDA x))
    (fun x => realOperatorEntry_diagonal_lower (A x) (hell x) k)
    H hH (fun x i => realOperatorEntry_apply (A x) (p.2 x) i) f (Lp.memLp f) hweakH
    (fun j => g j) (fun j => Lp.memLp (g j)) hder
  intro j
  by_cases hj : j = k
  · subst j
    refine ⟨hG.toLp G, ?_⟩
    apply hGD.congr_on volume (Eventually.of_forall (fun _ _ => rfl))
    filter_upwards [hG.coeFn_toLp] with x hx
    exact fun _ => hx.symm
  · exact ⟨g j, hder j hj⟩

end OAI.Analysis.PDE.Weak
