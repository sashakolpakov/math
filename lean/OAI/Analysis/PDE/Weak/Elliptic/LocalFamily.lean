import OAI.Analysis.PDE.Weak.Elliptic.DerivativeFamily
import OAI.Analysis.PDE.Weak.Elliptic.SmoothInterior

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- A local weak derivative hierarchy has a compactly supported global
representative hierarchy agreeing with the original field near the point. -/
theorem weakRegularity_local_family
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω) {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ Ω)
    {k : ℕ} {u : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : WeakRegularity Ω k u) :
    ∃ (V K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m))
      (U : List (Fin (m + 1)) → Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ IsCompact K ∧ K ⊆ Ω ∧
      (∀ᵐ y ∂volume, y ∈ V → U [] y = u y) ∧
      (∀ α, α.length ≤ k → ∀ᵐ y ∂volume, y ∉ K → U α y = 0) ∧
      (∀ α, α.length < k → ∀ i,
        HasWeakDirectionalDerivative volume (Pi.single i 1) (U α) (U (i :: α))) := by
  obtain ⟨η, V, hV, hxV, hVΩ, hη, hηs, hηsub, hηrange, hηone⟩ :=
    exists_cutoff_with_open_plateau hΩ hx
  let A : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ →L[ℝ] ℝ := fun y ↦ η y • ContinuousLinearMap.id ℝ ℝ
  have hA : ContDiff ℝ ∞ A := hη.smul contDiff_const
  have hAs : HasCompactSupport A := hηs.smul_right
  have hAsub : tsupport A ⊆ tsupport η := tsupport_smul_subset_left η _
  obtain ⟨M, hM⟩ := (smoothBounded_of_hasCompactSupport hA hAs).bound
  let v := fieldMultiplierCLM (μ := volume) A hA.continuous.aestronglyMeasurable
    (Eventually.of_forall hM) u
  have hv : SupportedRegularity (tsupport η) k v :=
    hu.compact_operator_mul A hA hAs hAsub (hAsub.trans hηsub) hM
  obtain ⟨U, hU, hUs, hUd⟩ := supportedRegularity_derivative_family hv
  refine ⟨V, tsupport η, U, hV, hxV, hVΩ, hηs, hηsub, ?_, hUs, hUd⟩
  rw [hU]
  filter_upwards [fieldMultiplierCLM_ae A hA.continuous.aestronglyMeasurable
    (Eventually.of_forall hM) u] with y hy
  intro hyV
  rw [hy]
  change η y * u y = u y
  rw [hηone y hyV, one_mul]

/-- The actual weak elliptic equation with smooth local data supplies the
complete compactly supported derivative family used in Sobolev embedding. -/
theorem smooth_elliptic_local_derivative_family
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {lam : ℝ} (hlam : 0 < lam) (k : ℕ)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (hell : ∀ x ∈ Ω, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐ x ∂volume, x ∈ Ω → f x = g x)
    (he : WeakDivergenceEquation Ω (fun y ↦ A y (p.2 y)) f)
    {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ Ω) :
    ∃ (V K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m))
      (U : List (Fin (m + 1)) → Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ IsCompact K ∧ K ⊆ Ω ∧
      (∀ᵐ y ∂volume, y ∈ V → U [] y = p.1 y) ∧
      (∀ α, α.length ≤ k → ∀ᵐ y ∂volume, y ∉ K → U α y = 0) ∧
      (∀ α, α.length < k → ∀ i,
        HasWeakDirectionalDerivative volume (Pi.single i 1) (U α) (U (i :: α))) := by
  obtain ⟨W, hW, hxW, hWΩ, hreg⟩ := smooth_interior_regular_near_point
    A hA hlam k hΩ hell p hp f g hg hfg he hx
  obtain ⟨V, K, U, hV, hxV, hVW, hK, hKW, hU, hUs, hUd⟩ :=
    weakRegularity_local_family hW hxW hreg.value.pred
  exact ⟨V, K, U, hV, hxV, hVW.trans hWΩ, hK, hKW.trans hWΩ, hU, hUs, hUd⟩

end OAI.Analysis.PDE.Weak
