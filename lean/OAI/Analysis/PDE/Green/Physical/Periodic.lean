import OAI.Analysis.PDE.Green.MovingFiberSmooth
import OAI.Analysis.PDE.Green.DensitySmooth

/-! Smoothness of actual periodic-cell physical fiber integrals. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet
open scoped ContDiff Matrix.Norms.Elementwise

def periodicPhysicalFiberIntegral {E : Type} {d k : ℕ}
    (a : ℝ) (τ : E → ℂ)
    (f : (E × (Fin k → ℝ)) × (Option (Fin d) → ℂ) → ℝ) (z : E) : ℝ :=
  ∫ x in Icc (0 : Fin k → ℝ) 1,
    ∫ q in {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (τ z) q < 0}, f ((z, x), q)

theorem contDiffOn_periodicPhysicalFiberIntegral {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {d k : ℕ} (a : ℝ) (ha : 0 < a) (τ : E → ℂ) (hτ : ContDiff ℝ ∞ τ)
    (f : (E × (Fin k → ℝ)) × (Option (Fin d) → ℂ) → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (periodicPhysicalFiberIntegral a τ f) {z | a < ‖τ z‖} := by
  have hinner := contDiffOn_physical_fiber_integral a ha
    (fun p : E × (Fin k → ℝ) => τ p.1) (hτ.comp contDiff_fst) f hf
  exact contDiffOn_compact_setIntegral volume isCompact_Icc measurableSet_Icc
    (Subset.rfl) isCompact_Icc.measure_lt_top
    (isOpen_lt continuous_const hτ.continuous.norm)
    (isOpen_lt continuous_const (hτ.continuous.comp continuous_fst).norm)
    _ hinner (by intros; assumption)

theorem contDiffOn_periodicPhysicalCombinedEnergy {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {d k n s : ℕ} (a : ℝ) (ha : 0 < a) (τ : E → ℂ) (hτ : ContDiff ℝ ∞ τ)
    (L : (E × (Fin k → ℝ)) × (Option (Fin d) → ℂ) → OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)
    (hL : ContDiff ℝ ∞ L) (e : Fin s → Quaternion ℝ) (lam : ℝ)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ ∞ A) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ}
    (hB : ContDiff ℝ ∞ B) (hu : ContDiff ℝ ∞ u) :
    ContDiffOn ℝ ∞
      (periodicPhysicalFiberIntegral a τ (fun p => combinedEnergyDensity e lam A B u (L p)))
      {z | a < ‖τ z‖} :=
  contDiffOn_periodicPhysicalFiberIntegral a ha τ hτ _
    ((contDiff_combinedEnergyDensity e lam hA hB hu).comp hL)

end OAI.Analysis.PDE.Green
