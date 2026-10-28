import OAI.Analysis.PDE.Weak.Elliptic.DifferentiatedEquation
import OAI.Analysis.PDE.Weak.Elliptic.Divergence

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

def coefficientPartial
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (j : Fin (m + 1)) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m :=
  fderiv ℝ A x (Pi.single j 1)

/-- Once the weak gradient has L² first derivatives, the differentiated
equation has an actual L² scalar load. The coefficient commutator is
computed by a proved weak product rule and divergence identity. -/
theorem differentiated_equation_L2
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ 2 A) {M D B : ℝ}
    (hM : ∀ x, ‖A x‖ ≤ M)
    (hD : ∀ j x, ‖coefficientPartial A j x‖ ≤ D)
    (hB : ∀ i j x, ‖coefficientPartial (coefficientPartial A j) i x‖ ≤ B)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (G : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (Gd : Fin (m + 1) → Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (hG : ∀ i, HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) G (Gd i))
    (f fd : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (j : Fin (m + 1))
    (hf : HasWeakDirectionalDerivativeOn volume Ω (Pi.single j 1) f fd)
    (hweak : WeakDivergenceEquation Ω (fun x ↦ A x (G x)) f) :
    ∃ F : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)),
      WeakDivergenceEquation Ω (fun x ↦ A x (Gd j x)) F := by
  have hA1 : ContDiff ℝ 1 A := hA.of_le (by norm_num)
  have hAj (i : Fin (m + 1)) : ContDiff ℝ 1 (coefficientPartial A i) :=
    (hA.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hAji (i : Fin (m + 1)) : Continuous (coefficientPartial (coefficientPartial A j) i) := by
    have hc := (hAj j).continuous_fderiv one_ne_zero
    exact hc.clm_apply continuous_const
  let R : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m := fun x ↦ coefficientPartial A j x (G x)
  let Rd : Fin (m + 1) → OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m := fun i x ↦
    coefficientPartial A j x (Gd i x) + coefficientPartial (coefficientPartial A j) i x (G x)
  have hR : MemLp R 2 volume :=
    fieldMultiplier_memLp (coefficientPartial A j) (hAj j).continuous.aestronglyMeasurable
      (Eventually.of_forall (hD j)) G
  have hRd (i : Fin (m + 1)) : MemLp (Rd i) 2 volume :=
    (fieldMultiplier_memLp (coefficientPartial A j) (hAj j).continuous.aestronglyMeasurable
      (Eventually.of_forall (hD j)) (Gd i)).add
      (fieldMultiplier_memLp (coefficientPartial (coefficientPartial A j) i)
        (hAji i).aestronglyMeasurable (Eventually.of_forall (hB i j)) G)
  have hRder (i : Fin (m + 1)) :
      HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) R (Rd i) :=
    (hG i).operator_apply volume (coefficientPartial A j) (hAj j) G (Gd i)
  obtain ⟨hr, heR⟩ := weak_negative_divergence hR Rd hRd hRder
  have heW := hweak.differentiate_coefficient A hA1 G (Gd j) (hG j) hf
  have hAG : MemLp (fun x ↦ A x (Gd j x)) 2 volume :=
    fieldMultiplier_memLp A hA1.continuous.aestronglyMeasurable (Eventually.of_forall hM) (Gd j)
  have he := heW.subtract_flux heR hAG hR (Lp.memLp fd) hr
  have hF : MemLp (fun x ↦ fd x - (-∑ i, Rd i x i)) 2 volume := (Lp.memLp fd).sub hr
  refine ⟨hF.toLp _, ?_⟩
  intro φ hφ hs hsub
  rw [he φ hφ hs hsub]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with x hx
  rw [hx]

end OAI.Analysis.PDE.Weak
