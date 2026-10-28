import OAI.NumberTheory.ArithmeticGroups.Lattices.UniformShortSpan

/-! # Frame Matrices -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.FrameMatrices.Construction

noncomputable section

section

/-! A compact set of bases representing all lattices whose covolumes stay
in a fixed positive interval and whose nonzero vectors stay away from zero.
This is the frame form of Mahler's compactness criterion. -/

open scoped Classical
open Set _root_.Module _root_.MeasureTheory

theorem continuous_basis_determinant
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) :
    Continuous (fun v : ι → E => b.det v) := by
  change Continuous (fun v : ι → E => (b.toMatrix v).det)
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (b.coord i).continuous_of_finiteDimensional.comp (continuous_apply j)

theorem compact_nondegenerate_frames
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) (R c D : ℝ) :
    IsCompact ({v : ι → E | ∀ i, ‖v i‖ ≤ R} ∩ {v | c ≤ |b.det v| * D}) := by
  have hcompact : IsCompact {v : ι → E | ∀ i, ‖v i‖ ≤ R} := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (isCompact_pi_infinite (fun _ : ι => isCompact_closedBall (0 : E) R))
  exact hcompact.inter_right (isClosed_le continuous_const
    ((continuous_basis_determinant b).abs.mul_const D))

theorem nondegenerate_frame_is_basis
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) {v : ι → E} {c D : ℝ} (hc : 0 < c)
    (hv : c ≤ |b.det v| * D) :
    LinearIndependent ℝ v ∧ Submodule.span ℝ (Set.range v) = ⊤ := by
  apply b.is_basis_iff_det.mpr
  apply isUnit_iff_ne_zero.mpr
  intro he
  simp only [he, abs_zero, zero_mul] at hv
  exact hc.not_ge hv

theorem exists_compact_lattice_frames
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (ε c C : ℝ)
    (hε : 0 < ε) (hc : 0 < c) :
    ∃ K : Set (Fin (finrank ℝ E) → E), IsCompact K ∧
      (∀ v ∈ K, LinearIndependent ℝ v ∧ Submodule.span ℝ (Set.range v) = ⊤) ∧
      ∀ (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
        c ≤ ZLattice.covolume Λ μ → ZLattice.covolume Λ μ ≤ C →
        (∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖x‖) →
        ∃ b : Basis (Fin (finrank ℝ E)) ℤ Λ, (fun i => (b i).val) ∈ K := by
  obtain ⟨R, _, hR⟩ := UniformShortSpan.Construction.exists_uniform_lattice_basis_bound μ ε C hε
  let b₀ := Module.finBasis ℝ E
  let D := μ.real (ZSpan.fundamentalDomain b₀)
  let K : Set (Fin (finrank ℝ E) → E) :=
    {v | ∀ i, ‖v i‖ ≤ R} ∩ {v | c ≤ |b₀.det v| * D}
  refine ⟨K, compact_nondegenerate_frames b₀ R c D,
    fun v hv => nondegenerate_frame_is_basis b₀ hc hv.2, ?_⟩
  intro Λ _ _ hlow hupp hgap
  obtain ⟨b, hb⟩ := hR Λ hupp hgap
  refine ⟨b, hb, ?_⟩
  change c ≤ |b₀.det ((↑) ∘ b)| * μ.real (ZSpan.fundamentalDomain b₀)
  rwa [← ZLattice.covolume_eq_det_mul_measureReal Λ μ b b₀]

end

/-! Compact lattice frames expressed as invertible matrices. -/

open scoped Classical
open Set _root_.Module _root_.MeasureTheory

theorem continuous_basis_matrix
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) :
    Continuous (fun v : ι → E => b.toMatrix v) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (b.coord i).continuous_of_finiteDimensional.comp (continuous_apply j)

theorem continuous_invertible_matrix_mk
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    (f : X → Matrix ι ι ℝ) (hf : Continuous f) (hdet : ∀ x, (f x).det ≠ 0) :
    Continuous (fun x => Matrix.GeneralLinearGroup.mkOfDetNeZero (f x) (hdet x)) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact hf
  · simp only [Matrix.GeneralLinearGroup.coe_inv]
    change Continuous (fun x => (f x)⁻¹)
    apply continuous_iff_continuousAt.mpr
    intro x
    apply (continuousAt_matrix_inv (f x) ?_).comp hf.continuousAt
    convert continuousAt_inv₀ (hdet x) using 1
    exact funext Ring.inverse_eq_inv

def matrixOfFrame
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (v : ι → E)
    (hv : LinearIndependent ℝ v ∧ Submodule.span ℝ (Set.range v) = ⊤) :
    Matrix.GeneralLinearGroup ι ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (b.toMatrix v)
    (isUnit_iff_ne_zero.mp (b.is_basis_iff_det.mp hv))

@[simp] theorem matrixOfFrame_val
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (v : ι → E)
    (hv : LinearIndependent ℝ v ∧ Submodule.span ℝ (Set.range v) = ⊤) :
    (matrixOfFrame b v hv).val = b.toMatrix v := rfl

theorem compact_frame_matrices
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E)
    {K : Set (ι → E)} (hK : IsCompact K)
    (hframe : ∀ v ∈ K, LinearIndependent ℝ v ∧ Submodule.span ℝ (Set.range v) = ⊤) :
    IsCompact (Set.range (fun v : K => matrixOfFrame b v.val (hframe v.val v.property))) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply isCompact_range
  apply continuous_invertible_matrix_mk
  exact (continuous_basis_matrix b).comp continuous_subtype_val

theorem exists_compact_lattice_matrices
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (b₀ : Basis (Fin (finrank ℝ E)) ℝ E) (ε c C : ℝ)
    (hε : 0 < ε) (hc : 0 < c) :
    ∃ K : Set (Matrix.GeneralLinearGroup (Fin (finrank ℝ E)) ℝ), IsCompact K ∧
      ∀ (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
        c ≤ ZLattice.covolume Λ μ → ZLattice.covolume Λ μ ≤ C →
        (∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖x‖) →
        ∃ b : Basis (Fin (finrank ℝ E)) ℤ Λ, ∃ M ∈ K,
          M.val = b₀.toMatrix (fun i => (b i).val) := by
  obtain ⟨S, hS, hframe, hΛ⟩ := exists_compact_lattice_frames μ ε c C hε hc
  let f := fun v : S => matrixOfFrame b₀ v.val (hframe v.val v.property)
  refine ⟨Set.range f, compact_frame_matrices b₀ hS hframe, ?_⟩
  intro Λ _ _ hlow hupp hgap
  obtain ⟨b, hb⟩ := hΛ Λ hlow hupp hgap
  exact ⟨b, f ⟨(fun i => (b i).val), hb⟩, ⟨⟨_, hb⟩, rfl⟩, rfl⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.FrameMatrices.Construction
