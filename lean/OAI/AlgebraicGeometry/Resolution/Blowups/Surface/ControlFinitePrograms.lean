import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ResidualFiniteExistence
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialOrderBound

/-! # Control Finite Programs -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ControlFinitePrograms.Construction

noncomputable section

/-! Every finite family of nonzero surface ideals has common full-boundary programs at an arbitrary positive control. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_surface_control_programs
    (b : ℕ) (hb : 0 < b) {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι]
    (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData)
    (hJ : ∀ i, J i ≠ ⊥) (hd : ∀ i, topologicalKrullDim (X i) ≤ 2)
    (D : ∀ i, β → (X i).IdealSheafData)
    (E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ]) :
    ∃ (m : ℕ) (schedule : ResidualSchedule.Construction.SurfaceResidualSchedule b m β (fun _ => 0)), ∀ i,
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData) (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (X i) (f i) (J i) Y g K),
        ResidualProgram.Construction.SurfaceResidualProgram b schedule (X i) (f i) (J i) (J i) (D i) Y g K P := by
  classical
  choose bounds hbounds using fun i => Global.DifferentialOrderBound.Construction.exists_global_complex_differential_order_bound (f i) (J i) (hJ i)
  let m := Finset.univ.sup bounds
  have hbound (i : ι) : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (f i) (J i) m = ⊤ :=
    Global.DifferentialFiltration.Construction.smoothDifferentialIdealSheaf_top_of_le (f i) (J i) (Finset.le_sup (Finset.mem_univ i)) (hbounds i)
  obtain ⟨schedule, hprogram⟩ := ResidualFiniteExistence.Construction.exists_finite_surface_residual_programs b hb m (fun _ : β => 0)
    X f J J hJ hd D E (fun i => by simp only [Global.MixedBoundary.Construction.boundaryMonomialSheaf, pow_zero, Finset.prod_const_one, one_mul]) hbound
  exact ⟨m, schedule, hprogram⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ControlFinitePrograms.Construction
