import OAI.Analysis.Fourier.WavePackets.Dirichlet.Padding

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Concentration
open scoped ContDiff Topology ComplexOrder

variable {m : ℕ} {P V ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 ≃L[ℝ] P × V} {b : Basis ι ℝ P}

theorem latticePeriodic_basis_add {E P V ι W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {f : E → W} (hf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f)
    (i : ι) (x : E) : f (x + e.symm (b i,0)) = f x := by
  have h := hf x ⟨b i, Submodule.subset_span (mem_range_self i)⟩
  have he : e.symm ((e x).1 + b i, (e x).2) = x + e.symm (b i,0) := by
    apply e.injective
    simp only [map_add, ContinuousLinearEquiv.apply_symm_apply]
    apply Prod.ext <;> simp
  simpa only [he] using h

theorem latticePeriodic_insertFourth {W : Type} {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 → W}
    (hf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (P := P × (Fin m → ℝ)) (V := V) (ι := ι ⊕ Fin m)
      (paddedLatticeSplit (m := m) (P := P) (V := V) e) (paddedLatticeBasis (m := m) b) f) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun y => f (insertFourth m y)) := by
  apply OAI.Analysis.PDE.Concentration.latticePeriodic_of_basis_periods
  intro i y
  have h := latticePeriodic_basis_add (P := P × (Fin m → ℝ)) (V := V) (ι := ι ⊕ Fin m)
    (paddedLatticeSplit (m := m) (P := P) (V := V) e) (paddedLatticeBasis (m := m) b)
    hf (Sum.inl i) (insertFourth m y)
  simpa only [paddedLatticeBasis, Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
    LinearMap.inl_apply, paddedLatticeSplit_symm, map_zero, add_zero, ← map_add] using h

theorem PeriodicQuaternionicSolution.descended_potential_hessian
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots e b)
    (S : PeriodicQuaternionicSolution (m := m) (s := 4) (slots := OAI.Analysis.Calculus.Quaternion.fourSlots)
      (P := P × (Fin m → ℝ)) (V := V) (ι := ι ⊕ Fin m)
      (e := paddedLatticeSplit e) (b := paddedLatticeBasis (m := m) b) D.padFourth)
    (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3) (hy : D.defining y < 0) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun z => D.background z + S.u (insertFourth m z)) y =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun x => D.padFourth.background x + S.u x) (insertFourth m y) := by
  have hf : ContDiff ℝ 2 (fun z => D.background z + S.u (insertFourth m z)) :=
    (D.background_smooth.add (S.smooth.comp (insertFourth m).contDiff)).of_le (by simp)
  have he := quaternionHessian_dropFourth hf (insertFourth m y)
  have hmem : {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 | D.defining (dropFourth m x) < 0} ∈ 𝓝 (insertFourth m y) :=
    (isOpen_lt (D.defining_smooth.continuous.comp (dropFourth m).continuous) continuous_const).mem_nhds
      (by change D.defining (dropFourth m (insertFourth m y)) < 0
          simpa only [dropFourth_insertFourth] using hy)
  have hg : (fun x => D.background (dropFourth m x) + S.u (insertFourth m (dropFourth m x))) =ᶠ[𝓝 (insertFourth m y)]
      (fun x => D.padFourth.background x + S.u x) := by
    filter_upwards [hmem] with x hx
    exact congrArg (fun t => D.background (dropFourth m x) + t)
      (S.independent_fourth D x hx.le).symm
  rw [OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots hg, dropFourth_insertFourth] at he
  exact he.symm

/-- A genuine four-slot solution descends to a genuine three-slot solution;
independence of the extra coordinates is proved by comparison. -/
def PeriodicQuaternionicSolution.descend
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots e b)
    (S : PeriodicQuaternionicSolution (m := m) (s := 4) (slots := OAI.Analysis.Calculus.Quaternion.fourSlots)
      (P := P × (Fin m → ℝ)) (V := V) (ι := ι ⊕ Fin m)
      (e := paddedLatticeSplit e) (b := paddedLatticeBasis (m := m) b) D.padFourth) :
    PeriodicQuaternionicSolution D where
  u y := S.u (insertFourth m y)
  smooth := S.smooth.comp (insertFourth m).contDiff
  periodic := latticePeriodic_insertFourth S.periodic
  boundary y hy := S.boundary _ (by simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth, dropFourth_insertFourth] using hy)
  admissible y hy := by
    rw [S.descended_potential_hessian D y hy]
    exact S.admissible _ (by simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth, dropFourth_insertFourth] using hy)
  equation y hy := by
    rw [S.descended_potential_hessian D y hy]
    simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth, dropFourth_insertFourth] using
      S.equation (insertFourth m y) (by simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth, dropFourth_insertFourth] using hy)

theorem threeSlotDirichlet_of_fourSlot [Nontrivial V] (hsolve : FourSlotDirichletExistence)
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots e b) : Nonempty (PeriodicQuaternionicSolution D) := by
  obtain ⟨S⟩ := hsolve m (P × (Fin m → ℝ)) V (ι ⊕ Fin m)
    (paddedLatticeSplit e) (paddedLatticeBasis (m := m) b) D.padFourth
  exact ⟨S.descend D⟩

end OAI.Analysis.Fourier.WavePackets
