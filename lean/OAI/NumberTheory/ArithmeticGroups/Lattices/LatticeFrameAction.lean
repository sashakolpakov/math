import OAI.NumberTheory.ArithmeticGroups.Lattices.FrameMatrices
import OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerRestriction

/-! # Lattice Frame Action -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeFrameAction.Construction

noncomputable section

section

/-! Matrix actions on lattice frames and integral change of basis. -/

open scoped Classical
open Set _root_.Module _root_.MeasureTheory

def matrixFrameAction
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) : Matrix.GeneralLinearGroup ι ℝ ≃* (E ≃ₗ[ℝ] E) :=
  (Units.mapEquiv (Matrix.toLinAlgEquiv b).toMulEquiv).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ E)

theorem matrixFrameAction_toLinearMap
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (g : Matrix.GeneralLinearGroup ι ℝ) :
    (matrixFrameAction b g).toLinearMap = Matrix.toLin b b g.val := rfl

theorem matrixFrameAction_det
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (g : Matrix.GeneralLinearGroup ι ℝ) :
    (matrixFrameAction b g).toLinearMap.det = g.val.det := by
  rw [matrixFrameAction_toLinearMap, ← LinearMap.det_toMatrix b, LinearMap.toMatrix_toLin]

theorem matrixFrameAction_ofFrame
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (v : ι → E)
    (hv : LinearIndependent ℝ v ∧ Submodule.span ℝ (Set.range v) = ⊤) (i : ι) :
    matrixFrameAction b (FrameMatrices.Construction.matrixOfFrame b v hv) (b i) = v i := by
  change (matrixFrameAction b (FrameMatrices.Construction.matrixOfFrame b v hv)).toLinearMap (b i) = v i
  rw [matrixFrameAction_toLinearMap, FrameMatrices.Construction.matrixOfFrame_val, Basis.toMatrix_eq_toMatrix_constr,
    Matrix.toLin_toMatrix, Basis.constr_basis]

def matrixFrameIntegralAction
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) : Matrix.GeneralLinearGroup ι ℝ →* (E ≃ₗ[ℤ] E) where
  toFun g := (matrixFrameAction b g).restrictScalars ℤ
  map_one' := by ext x; simp [matrixFrameAction]
  map_mul' g h := by ext x; simp only [map_mul]; rfl

theorem map_lattice_of_basis_images
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] (Λ Ω : Submodule ℤ E)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] [DiscreteTopology Ω] [IsZLattice ℝ Ω]
    (b : Basis ι ℤ Λ) (c : Basis ι ℤ Ω) (f : E →ₗ[ℝ] E)
    (h : ∀ i, f (b i).val = (c i).val) :
    Λ.map (f.restrictScalars ℤ) = Ω := by
  rw [← b.ofZLatticeBasis_span ℝ, Submodule.map_span, ← c.ofZLatticeBasis_span ℝ]
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext i
  simpa only [Function.comp_apply, Basis.ofZLatticeBasis_apply, LinearMap.restrictScalars_apply]
    using h i

theorem linearEquiv_measurePreserving_of_abs_det_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (e : E ≃ₗ[ℝ] E)
    (he : |e.toLinearMap.det| = 1) : MeasurePreserving e μ μ := by
  have hd : e.toLinearMap.det ≠ 0 := by
    intro h
    simp only [h, abs_zero] at he
    norm_num at he
  refine ⟨e.continuous_of_finiteDimensional.measurable, ?_⟩
  change Measure.map e.toLinearMap μ = μ
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hd, abs_inv, he]
  simp

theorem covolume_comap_of_abs_det_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (e : E ≃ₗ[ℝ] E)
    (he : |e.toLinearMap.det| = 1) :
    ZLattice.covolume (ZLattice.comap ℝ Λ e.toLinearMap) μ = ZLattice.covolume Λ μ := by
  exact ZLattice.covolume_comap Λ μ μ
    (e := e.toContinuousLinearEquiv) (linearEquiv_measurePreserving_of_abs_det_one μ e he)

end

/-! Compact matrix representatives for lattices with a uniform lower bound
on their nonzero vector lengths. -/

open scoped Classical
open Set _root_.Module _root_.MeasureTheory

theorem exists_compact_matrix_lattice_representatives
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin (finrank ℝ E)) ℤ Λ)
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set (Matrix.GeneralLinearGroup (Fin (finrank ℝ E)) ℝ), IsCompact K ∧
      ∀ g : Matrix.GeneralLinearGroup (Fin (finrank ℝ E)) ℝ,
        |g.val.det| = 1 →
        (∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖matrixFrameAction (b.ofZLatticeBasis ℝ) g x‖) →
        ∃ γ ∈ SubmoduleOrbit.Construction.submoduleImageStabilizer (matrixFrameIntegralAction (b.ofZLatticeBasis ℝ)) Λ,
          g * γ ∈ K := by
  let b₀ := b.ofZLatticeBasis ℝ
  let ρ := matrixFrameIntegralAction b₀
  let c := ZLattice.covolume Λ μ
  obtain ⟨K, hK, hrep⟩ := FrameMatrices.Construction.exists_compact_lattice_matrices μ b₀ ε c c hε
    (ZLattice.covolume_pos Λ μ)
  refine ⟨K, hK, ?_⟩
  intro g hg hgap
  let e := (matrixFrameAction b₀ g).toContinuousLinearEquiv
  let Ω := ZLattice.comap ℝ Λ e.symm.toLinearMap
  have hedet : |e.symm.toLinearMap.det| = 1 := by
    change |(matrixFrameAction b₀ g).symm.toLinearMap.det| = 1
    rw [LinearEquiv.det_coe_symm, abs_inv]
    change |(matrixFrameAction b₀ g).toLinearMap.det|⁻¹ = 1
    rw [matrixFrameAction_det, hg, inv_one]
  have hcov : ZLattice.covolume Ω μ = c :=
    covolume_comap_of_abs_det_one Λ μ e.symm.toLinearEquiv hedet
  have hΩgap : ∀ y ∈ Ω, y ≠ 0 → ε ≤ ‖y‖ := by
    intro y hy hy0
    have hx : e.symm y ∈ Λ := hy
    have hx0 : e.symm y ≠ 0 := fun he => hy0 (e.symm.injective (he.trans (map_zero e.symm).symm))
    have h := hgap (e.symm y) hx hx0
    change ε ≤ ‖e (e.symm y)‖ at h
    simpa only [e.apply_symm_apply] using h
  obtain ⟨B, M, hMK, hM⟩ := hrep Ω hcov.ge hcov.le hΩgap
  have hMact (i : Fin (finrank ℝ E)) : matrixFrameAction b₀ M (b i).val = (B i).val := by
    rw [← b.ofZLatticeBasis_apply ℝ Λ i]
    change (matrixFrameAction b₀ M).toLinearMap (b₀ i) = (B i).val
    rw [matrixFrameAction_toLinearMap, hM, Basis.toMatrix_eq_toMatrix_constr,
      Matrix.toLin_toMatrix, Basis.constr_basis]
  have hMmap : Λ.map (ρ M).toLinearMap = Ω :=
    map_lattice_of_basis_images Λ Ω b B (matrixFrameAction b₀ M).toLinearMap hMact
  have hgmap : Λ.map (ρ g).toLinearMap = Ω := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change e.symm (e x) ∈ Λ
      rw [e.symm_apply_apply]
      exact hx
    · intro hy
      refine ⟨e.symm y, hy, ?_⟩
      exact e.apply_symm_apply y
  have hgcomp : (ρ g⁻¹).toLinearMap.comp (ρ g).toLinearMap = LinearMap.id := by
    rw [map_inv]
    ext x
    exact (ρ g).symm_apply_apply x
  have hinvmap : Ω.map (ρ g⁻¹).toLinearMap = Λ := by
    rw [← hgmap, ← Submodule.map_comp, hgcomp, Submodule.map_id]
  refine ⟨g⁻¹ * M, ?_, ?_⟩
  · change Λ.map (ρ (g⁻¹ * M)).toLinearMap = Λ
    rw [map_mul]
    change Λ.map ((ρ g⁻¹).toLinearMap.comp (ρ M).toLinearMap) = Λ
    rw [Submodule.map_comp, hMmap, hinvmap]
  · simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hMK

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeFrameAction.Construction
