import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeFrameAction

/-! # Covolume Transport -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CovolumeTransport.Construction

noncomputable section

/-! Covolume transformation and the determinant of an integral lattice
automorphism. -/

open scoped Classical
open Set _root_.Module _root_.MeasureTheory

theorem covolume_of_linear_lattice_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ Ω : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    [DiscreteTopology Ω] [IsZLattice ℝ Ω]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (e : E ≃ₗ[ℝ] E)
    (he : Λ.map (e.toLinearMap.restrictScalars ℤ) = Ω) :
    ZLattice.covolume Ω μ = |e.toLinearMap.det| * ZLattice.covolume Λ μ := by
  let b := Free.chooseBasis ℤ Λ
  let b₀ := b.ofZLatticeBasis ℝ
  let b' := b.map ((e.restrictScalars ℤ).ofSubmodules Λ Ω he)
  have hbase : b₀.det (fun i => (b i).val) = 1 := by
    convert b₀.det_self using 1
    congr 1
    funext i
    exact (b.ofZLatticeBasis_apply ℝ Λ i).symm
  have himage : b₀.det (fun i => (b' i).val) = e.toLinearMap.det := by
    have hfun : (fun i => (b' i).val) = e.toLinearMap ∘ (fun i => (b i).val) := by
      funext i
      rfl
    rw [hfun, Basis.det_comp, hbase, mul_one]
  rw [ZLattice.covolume_eq_det_mul_measureReal Ω μ b' b₀,
    ZLattice.covolume_eq_det_mul_measureReal Λ μ b b₀]
  change |b₀.det (fun i => (b' i).val)| * _ =
    |e.toLinearMap.det| * (|b₀.det (fun i => (b i).val)| * _)
  rw [himage, hbase, abs_one, one_mul]

theorem lattice_automorphism_abs_det_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (e : E ≃ₗ[ℝ] E)
    (he : Λ.map (e.toLinearMap.restrictScalars ℤ) = Λ) : |e.toLinearMap.det| = 1 := by
  have h := covolume_of_linear_lattice_image Λ Λ μ e he
  have hc := ZLattice.covolume_pos Λ μ
  nlinarith

theorem matrix_lattice_stabilizer_abs_det_one
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (b : Basis ι ℝ E)
    {g : Matrix.GeneralLinearGroup ι ℝ}
    (hg : g ∈ SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ) :
    |g.val.det| = 1 := by
  rw [← LatticeFrameAction.Construction.matrixFrameAction_det b g]
  exact lattice_automorphism_abs_det_one Λ μ (LatticeFrameAction.Construction.matrixFrameAction b g) hg

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CovolumeTransport.Construction
