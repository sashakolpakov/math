import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OrdinaryKernelConstruction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FixedLieCharacter
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsFixedPoint
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsPointHeights

/-! # Points Ordinary Kernel Data -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointsOrdinaryKernelData.CM.CMOrdinary

noncomputable section

/-! Construct the original native ordinary kernel data directly from
the full CMPoints conclusion, choosing its actual coefficient labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
  {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
  (hsplit : j.HasSplitCoordinates M.extendedEmbedding) (R : M.GoodIntegralReduction q j)

include hM in
omit [IsGalois ℚ E] in
theorem dimension_eq : M.s = (M.s - 1) + 1 := by have h := hM.1; omega

theorem exists_kernelData (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.GeometricConclusion R) :
    ∃ labels : (Fin M.s × Bool) ≃ Gal(E/ℚ),
      ∃ hlabels : ∀ (v : Fin M.s) (b : Bool),
        labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b),
        labels (⟨0, hM.1⟩, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E ∧
        ∀ a : M.Family, Nonempty (OrdinaryKernelConstruction.CM.PositiveData.KernelDataAt
          (AbelianScheme.FrobeniusKernel.CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a)
          j M.extendedEmbedding hsplit labels (M.s - 1) (dimension_eq M hM)) := by
  obtain ⟨chosen, hc, hchosen, hlie⟩ := AbelianScheme.FrobeniusKernel.CMPointsFixedPoint.Construction.l45GeometricConclusion_fixedLieRanks M R hCMPoints
  obtain ⟨labels, hactive, hlabels, hmem, _⟩ := AbelianScheme.FrobeniusKernel.CMPointsModelLabels.Construction.exists_l45ModelLabels M hM chosen hc hchosen
  refine ⟨labels, hlabels, hactive, fun a => ?_⟩
  let D := AbelianScheme.FrobeniusKernel.CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a
  apply OrdinaryKernelConstruction.CM.PositiveData.construct D j M.extendedEmbedding hsplit labels
    (M.s - 1) (dimension_eq M hM)
  · intro x v
    exact AbelianScheme.FrobeniusKernel.CMPointsPointHeights.Construction.l45GeometricConclusion_fixedHeights M R hCMPoints a x.val (labels (v, false))
  · intro x
    have h := (hlie a x.val).1
    change AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (AbelianScheme.FrobeniusKernel.PointsGeometricPointData.Construction.l45FixedPointActionData M R a x.val).polarized.abelian
      (AbelianScheme.FrobeniusKernel.PointsGeometricPointData.Construction.l45FixedPointActionData M R a x.val).action
      (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j M.extendedEmbedding (labels (⟨0, _⟩, false))) 1
    rw [hactive]
    exact (FixedLieCharacter.CM.character_eq M j (PELModuli.CMPoints.Arithmetic.rationalConjugation E)) ▸ h
  · intro x v hv
    have hne : labels (v, false) ≠ PELModuli.CMPoints.Arithmetic.rationalConjugation E := by
      intro he
      have hi := labels.injective (he.trans hactive.symm)
      exact hv (congrArg (fun z : Fin M.s × Bool => z.1.val) hi)
    rcases (hlie a x.val).2 (labels (v, false)) (hmem v) hne with h | h
    · exact Or.inl ((FixedLieCharacter.CM.character_eq M j (labels (v, false))) ▸ h)
    · exact Or.inr ((FixedLieCharacter.CM.character_eq M j (labels (v, false))) ▸ h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointsOrdinaryKernelData.CM.CMOrdinary
