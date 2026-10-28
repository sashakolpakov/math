import OAI.Analysis.PDE.Weak.Elliptic.H1
import OAI.Analysis.PDE.Weak.Elliptic.Multiplier

noncomputable section
open Set _root_.MeasureTheory
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {X V : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : Measure X}

def scalarField (η : X → ℝ) (x : X) : V →L[ℝ] V :=
  η x • ContinuousLinearMap.id ℝ V

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem continuous_scalarField {η : X → ℝ} (hη : Continuous η) :
    Continuous (scalarField (V := V) η) := hη.smul continuous_const

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem norm_scalarField_le (η : X → ℝ) (x : X) :
    ‖scalarField (V := V) η x‖ ≤ |η x| := by
  rw [scalarField, norm_smul, Real.norm_eq_abs]
  simpa using mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := V))
    (abs_nonneg (η x))

def cutoffL2 (η : X → ℝ) (hη : Continuous η) {M : ℝ}
    (hM : ∀ x, |η x| ≤ M) : Lp V 2 μ →L[ℝ] Lp V 2 μ :=
  fieldMultiplierCLM (scalarField η) (continuous_scalarField hη).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ (norm_scalarField_le η x).trans (hM x))

theorem cutoffL2_ae (η : X → ℝ) (hη : Continuous η) {M : ℝ}
    (hM : ∀ x, |η x| ≤ M) (u : Lp V 2 μ) :
    cutoffL2 η hη hM u =ᵐ[μ] fun x ↦ η x • u x := by
  exact fieldMultiplierCLM_ae _ _ _ _

def vectorField (g : X → V) (x : X) : ℝ →L[ℝ] V :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (g x)

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem continuous_vectorField {g : X → V} (hg : Continuous g) :
    Continuous (vectorField g) := by
  unfold vectorField
  fun_prop

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem norm_vectorField_le (g : X → V) (x : X) :
    ‖vectorField g x‖ ≤ ‖g x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro c
  simp [vectorField, norm_smul, mul_comm]

def vectorProductL2 (g : X → V) (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) : Lp ℝ 2 μ →L[ℝ] Lp V 2 μ :=
  fieldMultiplierCLM (vectorField g) (continuous_vectorField hg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ (norm_vectorField_le g x).trans (hM x))

theorem vectorProductL2_ae (g : X → V) (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) (u : Lp ℝ 2 μ) :
    vectorProductL2 g hg hM u =ᵐ[μ] fun x ↦ u x • g x := by
  exact fieldMultiplierCLM_ae _ _ _ _

variable {m : ℕ}

def cutoffH1Pair (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ 1 η)
    {M K : ℝ} (hM : ∀ x, |η x| ≤ M) (hK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K) :
    H1Pair m →L[ℝ] H1Pair m :=
  ((cutoffL2 η hη.continuous hM).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (((cutoffL2 η hη.continuous hM).comp (ContinuousLinearMap.snd ℝ _ _)) +
      (vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK).comp
        (ContinuousLinearMap.fst ℝ _ _))

theorem cutoffH1Pair_value_ae (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ 1 η)
    {M K : ℝ} (hM : ∀ x, |η x| ≤ M) (hK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K)
    (p : H1Pair m) :
    (cutoffH1Pair η hη hM hK p).1 =ᵐ[volume] fun x ↦ η x * p.1 x :=
  cutoffL2_ae η hη.continuous hM p.1

theorem cutoffH1Pair_gradient_ae (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ 1 η)
    {M K : ℝ} (hM : ∀ x, |η x| ≤ M) (hK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K)
    (p : H1Pair m) :
    (cutoffH1Pair η hη hM hK p).2 =ᵐ[volume]
      fun x ↦ η x • p.2 x + p.1 x • OAI.Analysis.PDE.Variational.cellGradient η x := by
  change cutoffL2 η hη.continuous hM p.2 +
    vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK p.1 =ᵐ[volume] _
  filter_upwards [Lp.coeFn_add (cutoffL2 η hη.continuous hM p.2)
      (vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK p.1),
    cutoffL2_ae η hη.continuous hM p.2,
    vectorProductL2_ae (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK p.1] with x hx hy hz
  rw [hx]
  simp only [Pi.add_apply, hy, hz]

theorem cellGradient_mul {η u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hη : Differentiable ℝ η) (hu : Differentiable ℝ u) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    OAI.Analysis.PDE.Variational.cellGradient (fun y ↦ η y * u y) x =
      η x • OAI.Analysis.PDE.Variational.cellGradient u x + u x • OAI.Analysis.PDE.Variational.cellGradient η x := by
  ext i
  change fderiv ℝ (η * u) x (Pi.single i 1) = _
  rw [((hη x).hasFDerivAt.mul (hu x).hasFDerivAt).fderiv]
  simp

theorem cutoffH1Pair_smooth (η u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (hs : HasCompactSupport u)
    {M K : ℝ} (hM : ∀ x, |η x| ≤ M) (hK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K) :
    cutoffH1Pair η (hη.of_le (by simp)) hM hK (smoothH1Pair u hu hs) =
      smoothH1Pair (fun x ↦ η x * u x) (hη.mul hu) hs.mul_left := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [cutoffH1Pair_value_ae η (hη.of_le (by simp)) hM hK (smoothH1Pair u hu hs),
      smoothH1Pair_value_ae u hu hs,
      smoothH1Pair_value_ae (fun x ↦ η x * u x) (hη.mul hu) hs.mul_left] with x hx hy hz
    rw [hx, hy, hz]
  · apply Lp.ext
    filter_upwards [cutoffH1Pair_gradient_ae η (hη.of_le (by simp)) hM hK (smoothH1Pair u hu hs),
      smoothH1Pair_value_ae u hu hs, smoothH1Pair_gradient_ae u hu hs,
      smoothH1Pair_gradient_ae (fun x ↦ η x * u x) (hη.mul hu) hs.mul_left]
      with x hx hy hz hw
    rw [hx, hy, hz, hw, cellGradient_mul (hη.differentiable (by simp)) (hu.differentiable (by simp))]

/-- Smooth bounded cutoffs act on the genuine H¹ graph closure and localize
the admissible support of weak tests. -/
theorem H1Zero.cutoff {Ω Ω' : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {p : H1Pair m}
    (hp : p ∈ H1Zero Ω) (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η)
    {M K : ℝ} (hM : ∀ x, |η x| ≤ M) (hK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K)
    (hsupport : tsupport η ∩ Ω ⊆ Ω') :
    cutoffH1Pair η (hη.of_le (by simp)) hM hK p ∈ H1Zero Ω' := by
  have hc : IsClosed {q : H1Pair m |
      cutoffH1Pair η (hη.of_le (by simp)) hM hK q ∈ H1Zero Ω'} :=
    isClosed_closure.preimage (cutoffH1Pair η (hη.of_le (by simp)) hM hK).continuous
  apply closure_minimal (s := smoothH1Graph Ω) _ hc hp
  rintro q ⟨u, hu, hs, hΩ, rfl⟩
  change cutoffH1Pair η (hη.of_le (by simp)) hM hK (smoothH1Pair u hu hs) ∈ H1Zero Ω'
  rw [cutoffH1Pair_smooth η u hη hu hs hM hK]
  apply smoothH1Pair_mem_H1Zero
  intro x hx
  exact hsupport ⟨tsupport_mul_subset_left hx, hΩ (tsupport_mul_subset_right hx)⟩

end OAI.Analysis.PDE.Weak
