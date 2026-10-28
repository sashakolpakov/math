import OAI.Analysis.Calculus.SmoothExtension.HalfspaceReflection
import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension

/-! Differentiation of the single Seeley reflection series to every finite order. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.Calculus.FiniteExtension OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem seeleyTerm_iteratedFDeriv {N q : ℕ} (hq : q ≤ N)
    (ℓ : E →L[ℝ] ℝ) (ν : E) {f : E → F} (hf : ContDiff ℝ N f)
    (i : ReflectionIndex) (x : E) :
    iteratedFDeriv ℝ q (fun y => seeleyWeight i • f (OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i) y)) x =
      seeleyWeight i • (iteratedFDeriv ℝ q f (OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i) x)).compContinuousLinearMap
        (fun _ => OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i)) := by
  have hc : ContDiff ℝ q (fun y => f (OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i) y)) :=
    (hf.of_le (by exact_mod_cast hq)).comp (OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i)).contDiff
  rw [iteratedFDeriv_const_smul_apply' (a := seeleyWeight i) hc.contDiffAt]
  exact congrArg (fun A => seeleyWeight i • A)
    ((OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i)).iteratedFDeriv_comp_right hf x (by exact_mod_cast hq))

omit [CompleteSpace F] in
theorem seeleyTerm_jet_bound {N q : ℕ} (hq : q ≤ N)
    (ℓ : E →L[ℝ] ℝ) (ν : E) {f : E → F} (hf : ContDiff ℝ N f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, ‖iteratedFDeriv ℝ q f x‖ ≤ B)
    (i : ReflectionIndex) (x : E) :
    ‖iteratedFDeriv ℝ q (fun y => seeleyWeight i • f (OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i) y)) x‖ ≤
      (B*(‖ContinuousLinearMap.id ℝ E - ℓ.smulRight ν‖ + ‖ℓ.smulRight ν‖)^q) *
        (|seeleyWeight i| * |seeleyNode i|^q) := by
  rw [seeleyTerm_iteratedFDeriv hq ℓ ν hf i x,norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |seeleyWeight i| * (‖iteratedFDeriv ℝ q f (OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i) x)‖ *
        ‖OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i)‖^q) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa using (iteratedFDeriv ℝ q f (OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i) x)).norm_compContinuousLinearMap_le
        (fun _ : Fin q => OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i))
    _ ≤ |seeleyWeight i| * (B *
        ((‖ContinuousLinearMap.id ℝ E - ℓ.smulRight ν‖ + ‖ℓ.smulRight ν‖) * |seeleyNode i|)^q) := by
      gcongr
      · exact hb _
      · exact reflectionLinear_norm_le ℓ ν i
    _ = _ := by rw [mul_pow]; ring

theorem seeleyReflection_contDiff_and_jet {N : ℕ}
    (ℓ : E →L[ℝ] ℝ) (ν : E) {f : E → F} (hf : ContDiff ℝ N f)
    (B : ℕ → ℝ) (hB : ∀ q ≤ N, 0 ≤ B q)
    (hb : ∀ q ≤ N, ∀ x, ‖iteratedFDeriv ℝ q f x‖ ≤ B q) :
    ContDiff ℝ N (seeleyReflection ℓ ν f) ∧
      ∀ q ≤ N, ∀ x,
        iteratedFDeriv ℝ q (seeleyReflection ℓ ν f) x =
          ∑' i : ReflectionIndex, seeleyWeight i •
            (iteratedFDeriv ℝ q f (OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i) x)).compContinuousLinearMap
              (fun _ => OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i)) := by
  let v (q : ℕ) (i : ReflectionIndex) :=
    (B q*(‖ContinuousLinearMap.id ℝ E - ℓ.smulRight ν‖ + ‖ℓ.smulRight ν‖)^q) *
      (|seeleyWeight i| * |seeleyNode i|^q)
  have hv (q : ℕ) (_ : (q : ℕ∞) ≤ N) : Summable (v q) :=
    (seeley_abs_moment_summable q).mul_left _
  have hs (i : ReflectionIndex) : ContDiff ℝ N
      (fun y => seeleyWeight i • f (OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i) y)) :=
    (hf.comp (OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i)).contDiff).const_smul _
  have hd (q : ℕ) (i : ReflectionIndex) (x : E) (hq : (q : ℕ∞) ≤ N) :
      ‖iteratedFDeriv ℝ q (fun y => seeleyWeight i • f (OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i) y)) x‖ ≤ v q i := by
    have hqn : q ≤ N := by exact_mod_cast hq
    exact seeleyTerm_jet_bound hqn ℓ ν hf (B q) (hB q hqn) (hb q hqn) i x
  constructor
  · exact contDiff_tsum (N := (N : ℕ∞)) hs hv hd
  · intro q hq x
    unfold seeleyReflection
    rw [iteratedFDeriv_tsum_apply (N := (N : ℕ∞)) hs hv hd (by exact_mod_cast hq)]
    apply tsum_congr
    intro i
    exact seeleyTerm_iteratedFDeriv hq ℓ ν hf i x

theorem seeleyExtension_contDiff_of_bounded_jets {N : ℕ}
    (ℓ : E →L[ℝ] ℝ) (ν : E) {f : E → F} (hf : ContDiff ℝ N f)
    (B : ℕ → ℝ) (hB : ∀ q ≤ N, 0 ≤ B q)
    (hb : ∀ q ≤ N, ∀ x, ‖iteratedFDeriv ℝ q f x‖ ≤ B q) :
    ContDiff ℝ N (OAI.Analysis.PDE.Schauder.levelGlue ℓ f (seeleyReflection ℓ ν f)) := by
  obtain ⟨hs,hjet⟩ := seeleyReflection_contDiff_and_jet ℓ ν hf B hB hb
  apply HasFTaylorSeriesUpTo.contDiff
  apply OAI.Analysis.Calculus.FiniteExtension.hasFTaylorSeriesUpTo_levelGlue ℓ ℓ.continuous f (seeleyReflection ℓ ν f)
    (ftaylorSeries ℝ f) (ftaylorSeries ℝ (seeleyReflection ℓ ν f))
    (hf.ftaylorSeries.hasFTaylorSeriesUpToOn _) (hs.ftaylorSeries.hasFTaylorSeriesUpToOn _)
  intro q hq x hx
  change iteratedFDeriv ℝ q f x = iteratedFDeriv ℝ q (seeleyReflection ℓ ν f) x
  rw [hjet q hq x]
  simp_rw [OAI.Analysis.Calculus.FiniteExtension.reflectionLinear_boundary ℓ ν _ hx]
  exact (seeley_jet_moments ℓ ν (iteratedFDeriv ℝ q f x)).symm

theorem seeleyExtension_contDiff_of_compact {N : ℕ}
    (ℓ : E →L[ℝ] ℝ) (ν : E) {f : E → F} (hf : ContDiff ℝ N f)
    (hc : HasCompactSupport f) : ContDiff ℝ N (OAI.Analysis.PDE.Schauder.levelGlue ℓ f (seeleyReflection ℓ ν f)) := by
  have hb (q : ℕ) (hq : q ≤ N) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedFDeriv ℝ q f x‖ ≤ B := by
    obtain ⟨B,hB⟩ := (hf.continuous_iteratedFDeriv (by exact_mod_cast hq)).bounded_above_of_compact_support
      (hc.iteratedFDeriv q)
    exact ⟨max 0 B,le_max_left _ _,fun x => (hB x).trans (le_max_right _ _)⟩
  choose B hB0 hB using hb
  let C (q : ℕ) := if hq : q ≤ N then B q hq else 0
  apply seeleyExtension_contDiff_of_bounded_jets ℓ ν hf C
  · intro q hq
    simpa only [C,dite_eq_left hq] using hB0 q hq
  · intro q hq x
    simpa only [C,dite_eq_left hq] using hB q hq x

end OAI.Analysis.Calculus.SmoothExtension
