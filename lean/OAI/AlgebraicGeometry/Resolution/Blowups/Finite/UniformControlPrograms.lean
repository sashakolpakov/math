import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DimensionControlProgramSystems
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.FiniteDimension

/-! # Uniform Control Programs -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.UniformControlPrograms.Construction

noncomputable section

/-! Every finite compact smooth integral complex family has a shared actual program schedule, without a supplied dimension bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_uniform_control_programs
    (b : ℕ) (hb : 0 < b) {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι]
    (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData)
    (hJ : ∀ i, J i ≠ ⊥) (D : ∀ i, β → (X i).IdealSheafData)
    (E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ]) :
    ∃ (d : ℕ) (schedule : (DimensionControlProgramSystems.Construction.finiteDimensionControlProgramSystem d).Schedule b β), ∀ i,
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (X i) (f i) (J i) Y g K),
        (DimensionControlProgramSystems.Construction.finiteDimensionControlProgramSystem d).Program schedule (f i) (J i) (D i) P := by
  classical
  choose bounds hbounds using fun i => Global.FiniteDimension.Construction.exists_global_complex_dimension_bound (f i)
  let d := Finset.univ.sup bounds
  have hd (i : ι) : topologicalKrullDim (X i) ≤ (d + 2 : ℕ) :=
    (hbounds i).trans (Nat.cast_le.mpr ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_add_right d 2)))
  obtain ⟨schedule, hs⟩ := (DimensionControlProgramSystems.Construction.finiteDimensionControlProgramSystem d).finitePrograms b hb X f J hJ hd D E
  exact ⟨d, schedule, hs⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.UniformControlPrograms.Construction
