import OAI.Analysis.PDE.Weak.Elliptic.RegularDivergence
import OAI.Analysis.PDE.Weak.Elliptic.DifferentiatedEquation

noncomputable section
open Set _root_.MeasureTheory Filter
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- The explicitly differentiated scalar source retains all available
weak derivatives of the source and the gradient commutator terms. -/
theorem differentiated_equation_regular
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) (hA : SmoothBounded A)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    (G : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (Gd : Fin (m + 1) → Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (hG : ∀ i, HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) G (Gd i))
    (hGreg : WeakRegularity Ω k G) (hGdreg : ∀ i, WeakRegularity Ω k (Gd i))
    (f fd : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (hfdreg : WeakRegularity Ω k fd) (j : Fin (m + 1))
    (hf : HasWeakDirectionalDerivativeOn volume Ω (Pi.single j 1) f fd)
    (hweak : WeakDivergenceEquation Ω (fun x ↦ A x (G x)) f) :
    ∃ F : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)),
      WeakRegularity Ω k F ∧ WeakDivergenceEquation Ω (fun x ↦ A x (Gd j x)) F := by
  let Aj := coordinateDerivative A j
  have hAj : SmoothBounded Aj := hA.partial j
  obtain ⟨M, hM⟩ := hA.bound
  obtain ⟨D, hD⟩ := hAj.bound
  have hAji (i : Fin (m + 1)) : SmoothBounded (coordinateDerivative Aj i) := hAj.partial i
  choose B hB using fun i ↦ (hAji i).bound
  let T := fieldMultiplierCLM (μ := volume) Aj hAj.1.continuous.aestronglyMeasurable (Eventually.of_forall hD)
  let Ti := fun i ↦ fieldMultiplierCLM (μ := volume) (coordinateDerivative Aj i)
    (hAji i).1.continuous.aestronglyMeasurable (Eventually.of_forall (hB i))
  let R := T G
  let Rd := fun i ↦ T (Gd i) + Ti i G
  have hRdreg (i : Fin (m + 1)) : WeakRegularity Ω k (Rd i) :=
    ((hGdreg i).operator_mul Aj hAj hD).add
      (hGreg.operator_mul (coordinateDerivative Aj i) (hAji i) (hB i))
  have hRcoe : (R : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m) =ᵐ[volume] fun x ↦ Aj x (G x) :=
    fieldMultiplierCLM_ae Aj hAj.1.continuous.aestronglyMeasurable (Eventually.of_forall hD) G
  have hRder (i : Fin (m + 1)) :
      HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) R (Rd i) := by
    have hr := (hG i).operator_apply volume Aj (hAj.1.of_le (by simp)) G (Gd i)
    apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.congr_on volume hr
    · filter_upwards [hRcoe] with x hx
      exact fun _ ↦ hx.symm
    · filter_upwards [fieldMultiplierCLM_ae Aj hAj.1.continuous.aestronglyMeasurable
        (Eventually.of_forall hD) (Gd i),
        fieldMultiplierCLM_ae (coordinateDerivative Aj i) (hAji i).1.continuous.aestronglyMeasurable
          (Eventually.of_forall (hB i)) G, Lp.coeFn_add (T (Gd i)) (Ti i G)] with x hx hy hz
      intro _
      change Aj x (Gd i x) + fderiv ℝ Aj x (Pi.single i 1) (G x) = Rd i x
      rw [hz]
      change Aj x (Gd i x) + fderiv ℝ Aj x (Pi.single i 1) (G x) = T (Gd i) x + Ti i G x
      rw [hx, hy]
      rfl
  obtain ⟨divR, hdivreg, heR⟩ := weak_negative_divergence_regular R Rd hRdreg hRder
  have heW := hweak.differentiate_coefficient A (hA.1.of_le (by simp)) G (Gd j) (hG j) hf
  have heW' : WeakDivergenceEquation Ω (fun x ↦ A x (Gd j x) + R x) fd := by
    apply OAI.Analysis.PDE.Variational.weakEquation_congr_on heW (subset_refl _)
    · filter_upwards [hRcoe] with x hx
      intro _
      rw [hx]
      rfl
    · exact Eventually.of_forall fun _ _ ↦ rfl
  have hAG : MemLp (fun x ↦ A x (Gd j x)) 2 volume :=
    fieldMultiplier_memLp A hA.1.continuous.aestronglyMeasurable (Eventually.of_forall hM) (Gd j)
  have he := heW'.subtract_flux heR hAG (Lp.memLp R) (Lp.memLp fd) (Lp.memLp divR)
  refine ⟨fd - divR, hfdreg.sub hdivreg, ?_⟩
  intro φ hφ hs hsub
  rw [he φ hφ hs hsub]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub fd divR] with x hx
  rw [hx]
  rfl

end OAI.Analysis.PDE.Weak
