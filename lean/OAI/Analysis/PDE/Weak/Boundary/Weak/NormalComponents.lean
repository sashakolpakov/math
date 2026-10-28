import OAI.Analysis.PDE.Weak.Boundary.TestDensity
import OAI.Analysis.PDE.Weak.Elliptic.Product

/-! Mixed distributional derivatives recover the normal derivatives of
the tangential components of an H¹ gradient. -/

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem HasWeakDirectionalDerivativeOn.scalar_component
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {v : OAI.Analysis.PDE.Variational.CellCoordinates m}
    {u g : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m}
    (hd : HasWeakDirectionalDerivativeOn volume Ω v u g) (j : Fin (m + 1)) :
    HasWeakDirectionalDerivativeOn volume Ω v (fun x => u x j) (fun x => g x j) := by
  intro φ hφ hs hΩ
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using hd.component j φ hφ hs hΩ

theorem H1Zero.mixed_weak_derivative
    {Ω Ω₀ : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω) {p : H1Pair m}
    (hp : p ∈ H1Zero Ω₀) (i k : Fin (m + 1))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m) (hg : MemLp g 2 volume)
    (hd : HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) p.2 g) :
    HasWeakDirectionalDerivativeOn volume Ω (Pi.single k 1)
      (fun x => p.2 x i) (fun x => g x k) := by
  apply hasWeakDirectionalDerivativeOn_of_smooth volume hΩ _ _
    (memLp_cell_component (Lp.memLp p.2) i) (memLp_cell_component hg k)
  intro φ hφ hs hsub
  have he := hd.component k φ (hφ.of_le (by simp)) hs hsub
  rw [OAI.Analysis.PDE.Weak.H1Zero.mixed_weak_pairing hp i k φ (hφ.of_le (by simp)) hs] at he
  exact he

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

omit [SecondCountableTopology X] in
theorem HasWeakDirectionalDerivativeOn.scalar_mul
    (μ : Measure X) [IsLocallyFiniteMeasure μ] {Ω : Set X} {w : X}
    (a : X → ℝ) (ha : ContDiff ℝ 1 a) {u g : X → ℝ}
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ)
    (hd : HasWeakDirectionalDerivativeOn μ Ω w u g) :
    HasWeakDirectionalDerivativeOn μ Ω w (fun x => a x * u x)
      (fun x => a x * g x + fderiv ℝ a x w * u x) := by
  let A : X → ℝ →L[ℝ] ℝ := fun x => a x • ContinuousLinearMap.id ℝ ℝ
  have hA : ContDiff ℝ 1 A := ha.smul contDiff_const
  have hDA (x : X) : fderiv ℝ A x w = fderiv ℝ a x w • ContinuousLinearMap.id ℝ ℝ := by
    exact congrArg (fun L => L w)
      ((ha.differentiable one_ne_zero x).hasFDerivAt.smul_const (ContinuousLinearMap.id ℝ ℝ)).fderiv
  have he := hd.operator_apply_memLp μ A hA hu hg
  simpa only [hDA, A, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul] using he

end OAI.Analysis.PDE.Weak
