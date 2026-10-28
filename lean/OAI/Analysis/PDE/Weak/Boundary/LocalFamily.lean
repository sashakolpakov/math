import OAI.Analysis.PDE.Weak.Boundary.DerivativeFamily
import OAI.Analysis.PDE.Weak.Elliptic.SmoothInterior

noncomputable section
open Set _root_.MeasureTheory Filter
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Localization retains all derivatives on the ambient domain, including
when the compact cutoff crosses its boundary. -/
theorem weakRegularity_local_family_on
    {Ω V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hV : IsOpen V) {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ V)
    {k : ℕ} {u : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : WeakRegularity (Ω ∩ V) k u) :
    ∃ (W K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m))
      (U : List (Fin (m + 1)) → Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))),
      IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ IsCompact K ∧ K ⊆ V ∧
      (∀ᵐ y ∂volume, y ∈ W → U [] y = u y) ∧
      (∀ α, α.length ≤ k → ∀ᵐ y ∂volume, y ∉ K → U α y = 0) ∧
      (∀ α, α.length < k → ∀ i,
        HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) (U α) (U (i :: α))) := by
  obtain ⟨η, W, hW, hxW, hWV, hη, hηs, hηsub, _, hηone⟩ :=
    exists_cutoff_with_open_plateau hV hx
  let A : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ →L[ℝ] ℝ := fun y => η y • ContinuousLinearMap.id ℝ ℝ
  have hA : ContDiff ℝ ∞ A := hη.smul contDiff_const
  have hAs : HasCompactSupport A := hηs.smul_right
  have hAsub : tsupport A ⊆ tsupport η := tsupport_smul_subset_left η _
  obtain ⟨M, hM⟩ := (smoothBounded_of_hasCompactSupport hA hAs).bound
  let v := fieldMultiplierCLM (μ := volume) A hA.continuous.aestronglyMeasurable
    (Eventually.of_forall hM) u
  have hv : SupportedRegularityOn Ω (tsupport η) k v :=
    hu.compact_operator_mul_on A hA hAs hAsub (hAsub.trans hηsub) hM
  obtain ⟨U, hU, hUs, hUd⟩ := supportedRegularityOn_derivative_family hv
  refine ⟨W, tsupport η, U, hW, hxW, hWV, hηs, hηsub, ?_, hUs, hUd⟩
  rw [hU]
  filter_upwards [fieldMultiplierCLM_ae A hA.continuous.aestronglyMeasurable
    (Eventually.of_forall hM) u] with y hy
  intro hyW
  rw [hy]
  change η y * u y = u y
  rw [hηone y hyW, one_mul]

end OAI.Analysis.PDE.Weak
