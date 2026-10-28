import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.HistoryProgramAuxiliary
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DimensionLogarithmicPrograms

/-! # Dimension Auxiliary Programs -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DimensionAuxiliaryPrograms.Construction

noncomputable section

/-! A finite family of auxiliary boundary problems shares one complete logarithmic schedule. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_dimension_auxiliary_programs {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d)
    (n : ℕ) {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι]
    (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData)
    (hJ : ∀ i, J i ≠ ⊥) (hd : ∀ i, topologicalKrullDim (X i) ≤ (d + 1 : ℕ))
    (D : ∀ i, β → (X i).IdealSheafData) (A : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ]) (j : β) :
    ∃ schedule : Dimension.LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n {l : β // l ≠ j}, ∀ i,
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (X i) (f i) (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal (J i) (D i j) (n + 1)) Y g K),
        Dimension.HistoryProgramAuxiliary.Construction.DimensionAuxiliaryProgram 𝒮 j schedule (X i) (f i) (J i) (D i) Y g K P := by
  classical
  let B (i : ι) := Classical.choice (A i).exists_modelAtlas
  let γ := {l : β // l ≠ j}
  let e : γ ↪ β := ⟨Subtype.val, Subtype.val_injective⟩
  let E (i : ι) (l : γ) := D i (e l)
  let AE (i : ι) : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (E i) [Finset.univ] :=
    (A i).pullbackLabels (fun l => some (e l))
      (fun a b s ha hb => e.injective (Option.some_injective _ (ha.trans hb.symm))) (E i) (fun _ => rfl)
  have hlog (i : ι) : ((B i).reindex e).logarithmicIdeal (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal (J i) (D i j) (n + 1)) (n + 1) = ⊤ :=
    (B i).old_boundary_auxiliary_logarithmic_bound j e (fun l h => l.property h.symm) (J i) (D i j) le_rfl (n + 1)
  have haux (i : ι) : GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal (J i) (D i j) (n + 1) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (hJ i) le_sup_left
  exact DimensionLogarithmicPrograms.Construction.exists_finite_dimension_logarithmic_programs 𝒮 n X f
    (fun i => GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal (J i) (D i j) (n + 1)) haux hd E AE (fun i => (B i).reindex e) hlog

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DimensionAuxiliaryPrograms.Construction
