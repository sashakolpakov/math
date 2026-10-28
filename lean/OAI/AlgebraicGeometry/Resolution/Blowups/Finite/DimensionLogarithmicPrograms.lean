import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.LogarithmicProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundedComponent
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DimensionCoefficientPrograms

/-! # Dimension Logarithmic Programs -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DimensionLogarithmicPrograms.Construction

noncomputable section

/-! Finite logarithmic families in the next dimension share one complete coefficient schedule after canonical component clearing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_dimension_logarithmic_programs {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d)
    (n : ℕ) {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι]
    (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData)
    (hJ : ∀ i, J i ≠ ⊥) (hd : ∀ i, topologicalKrullDim (X i) ≤ (d + 1 : ℕ))
    (D : ∀ i, β → (X i).IdealSheafData) (E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ])
    (G : ∀ i, GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas (f i) (D i))
    (hlog : ∀ i, (G i).logarithmicIdeal (J i) (n + 1) = ⊤) :
    ∃ schedule : Dimension.LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n β, ∀ i,
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (X i) (f i) (J i) Y g K),
        Dimension.LogarithmicProgram.Construction.DimensionLogarithmicProgram 𝒮 schedule (X i) (f i) (J i) (D i) Y g K P := by
  classical
  let A (i : ι) := Classical.choice (BoundedComponent.Construction.exists_bounded_component_prefix (f i) (J i) n (D i) (E i) (G i) (hlog i))
  let : ∀ i, Smooth (A i).structureMap := fun i => (A i).program.endpoint_smooth
  let : ∀ i, IsIntegral (A i).endpoint := fun i => (A i).program.endpoint_integral
  let : ∀ i, IsLocallyNoetherian (A i).endpoint := fun i => LocallyOfFiniteType.isLocallyNoetherian (A i).structureMap
  let : ∀ i, CompactSpace (A i).endpoint := fun i => QuasiCompact.compactSpace_of_compactSpace (A i).program.toBase
  obtain ⟨schedule, hs⟩ := DimensionCoefficientPrograms.Construction.exists_finite_bounded_dimension_coefficient_programs 𝒮 n
    (fun i => (A i).endpoint) (fun i => (A i).structureMap) (fun i => (A i).ideal)
    (fun i => (A i).program.endpoint_ideal_ne_bot (hJ i))
    (fun i => (A i).program.endpoint_dimension_le (d + 1) (hd i))
    (fun i => (A i).program.boundaryAtLength (D i) _ (A i).count)
    (fun i => (A i).boundaryAtlas) (fun i => (A i).model) (fun i => (A i).logarithmic)
    (fun i => (A i).coefficientAtlas) (fun i => (A i).bound) (fun i => (A i).coefficientBound)
  refine ⟨schedule, ?_⟩
  intro i
  obtain ⟨Y, g, K, Q, hQ⟩ := hs i
  exact ⟨Y, g, K, (A i).program.append Q,
    .component (A i).initialAtlas (A i).centerAtlas (A i).program (A i).centers
      (A i).count (A i).uniform Q hQ⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DimensionLogarithmicPrograms.Construction
