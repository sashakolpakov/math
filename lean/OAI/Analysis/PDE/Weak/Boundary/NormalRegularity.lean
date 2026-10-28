import OAI.Analysis.PDE.Weak.Boundary.DiagonalFormula
import OAI.Analysis.PDE.Weak.Boundary.RegularityVector
import OAI.Analysis.PDE.Weak.Boundary.Weak.Vector

/-! The equation transfers every finite weak-derivative order from the
tangential Hessian entries to the missing normal entry. -/

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem H1Zero.normal_gradient_regular
    {Ω Ω₀ : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω) {p : H1Pair m}
    (hp : p ∈ H1Zero Ω₀) (k : Fin (m + 1)) (N : ℕ)
    (a : Fin (m + 1) → Fin (m + 1) → OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (ha : ∀ i j, SmoothBounded (a i j))
    (hinv : SmoothBounded (fun x => (a k k x)⁻¹))
    {M D lam : ℝ} (hlam : 0 < lam)
    (hM : ∀ i j x, ‖a i j x‖ ≤ M)
    (hD : ∀ i j l x, ‖fderiv ℝ (a i j) x (Pi.single l 1)‖ ≤ D)
    (hpos : ∀ x, lam ≤ a k k x)
    (H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m) (hH : MemLp H 2 volume)
    (hcoef : ∀ x i, H x i = ∑ j, a i j x * p.2 x j)
    (f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hf : MemLp f 2 volume)
    (hweak : WeakDivergenceEquation Ω H f)
    (g : Fin (m + 1) → OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m)
    (hg : ∀ i, MemLp (g i) 2 volume)
    (hd : ∀ i, i ≠ k → HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) p.2 (g i))
    (hpreg : FunctionWeakRegularity Ω N p.2) (hfreg : FunctionWeakRegularity Ω N f)
    (hgreg : ∀ i, i ≠ k → FunctionWeakRegularity Ω N (g i)) :
    ∃ G : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)),
      HasWeakDirectionalDerivativeOn volume Ω (Pi.single k 1) p.2 G ∧
      WeakRegularity Ω N G := by
  let ν : Fin (m+1) := k
  let B : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ := fun x =>
    (-f x -
      ∑ i ∈ Finset.univ.erase ν, ∑ j,
        (a i j x * g i x j + fderiv ℝ (a i j) x (Pi.single i 1) * p.2 x j) -
      ∑ j ∈ Finset.univ.erase ν,
        (a ν j x * g j x ν + fderiv ℝ (a ν j) x (Pi.single ν 1) * p.2 x j) -
      fderiv ℝ (a ν ν) x (Pi.single ν 1) * p.2 x ν) / a ν ν x
  obtain ⟨hB, hdB⟩ := OAI.Analysis.PDE.Weak.H1Zero.normal_diagonal_formula hΩ hp ν a (fun i j => (ha i j).1)
    hlam hM hD hpos H hH hcoef f hf hweak g hg hd
  have hpart (i j l) (hi : i ≠ ν) : FunctionWeakRegularity Ω N (fun x =>
      a i j x * g i x l + fderiv ℝ (a i j) x (Pi.single i 1) * p.2 x j) :=
    ((hgreg i hi).component l |>.scalar_mul (a i j) (ha i j)).add
      ((hpreg.component j).scalar_mul _ ((ha i j).partial i))
  have ht : FunctionWeakRegularity Ω N (fun x => ∑ i ∈ Finset.univ.erase ν, ∑ j,
      (a i j x * g i x j + fderiv ℝ (a i j) x (Pi.single i 1) * p.2 x j)) := by
    apply OAI.Analysis.PDE.Weak.FunctionWeakRegularity.finset_sum
    intro i hi
    apply OAI.Analysis.PDE.Weak.FunctionWeakRegularity.finset_sum
    intro j _
    exact hpart i j j (Finset.mem_erase.mp hi).1
  have hv : FunctionWeakRegularity Ω N (fun x => ∑ j ∈ Finset.univ.erase ν,
      (a ν j x * g j x ν + fderiv ℝ (a ν j) x (Pi.single ν 1) * p.2 x j)) := by
    apply OAI.Analysis.PDE.Weak.FunctionWeakRegularity.finset_sum
    intro j hj
    exact ((hgreg j (Finset.mem_erase.mp hj).1).component ν |>.scalar_mul (a ν j) (ha ν j)).add
      ((hpreg.component j).scalar_mul _ ((ha ν j).partial ν))
  have hnum := ((hfreg.neg.sub ht).sub hv).sub
    ((hpreg.component ν).scalar_mul _ ((ha ν ν).partial ν))
  have hBreg : FunctionWeakRegularity Ω N B := by
    have hh := hnum.scalar_mul (fun x => (a ν ν x)⁻¹) hinv
    simpa only [B, coordinateDerivative, div_eq_mul_inv, mul_comm] using hh
  let W : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m :=
    fun x => WithLp.toLp 2 (fun j => if j = ν then B x else g j x ν)
  have hW : MemLp W 2 volume := by
    apply MemLp.of_eval_piLp
    intro j
    by_cases hj : j = ν
    · subst j
      simpa [W, B, ν] using hB
    · simpa [W, hj] using memLp_cell_component (hg j) ν
  have hWreg : FunctionWeakRegularity Ω N W := by
    apply OAI.Analysis.PDE.Weak.FunctionWeakRegularity.of_components
    intro j
    by_cases hj : j = ν
    · subst j
      simpa [W] using hBreg
    · simpa [W, hj] using (hgreg j hj).component ν
  have hdW : HasWeakDirectionalDerivativeOn volume Ω (Pi.single ν 1) p.2 W := by
    apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.of_scalar_components (Lp.memLp p.2) hW
    intro j
    by_cases hj : j = ν
    · subst j
      simpa [W, B, ν] using hdB
    · simpa [W, hj] using OAI.Analysis.PDE.Weak.H1Zero.mixed_weak_derivative hΩ hp j ν (g j) (hg j) (hd j hj)
  refine ⟨hW.toLp W, ?_, hWreg.toLp hW⟩
  apply hdW.congr_on volume (Eventually.of_forall fun _ _ => rfl)
  filter_upwards [hW.coeFn_toLp] with x hx
  exact fun _ => hx.symm

end OAI.Analysis.PDE.Weak
