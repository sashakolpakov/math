import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointsOrdinaryKernelData
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RestrictedPlace
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FixedLieCharacter
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsFixedPoint
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsPointHeights

/-! # Restricted Ordinary Kernel Data -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedOrdinaryKernelData.CM.Ordinary

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

local notation "j₀" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RestrictedPlace.CM.choice M j
local notation "hs₀" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RestrictedPlace.CM.splitCoordinates M j hsplit

omit [IsGalois ℚ E] in
theorem character_eq (τ : Gal(E/ℚ)) : AbelianScheme.FrobeniusKernel.PointsPointLieRanks.Construction.l45FixedLieCharacter M (j := j) τ =
    RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter (k := AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) j₀ M.iota τ := by
  refine (FixedLieCharacter.CM.character_eq M j τ).trans ?_
  change RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockResidueCast.comp (j.residueCharacter M.extendedEmbedding τ 1) =
    RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockResidueCast.comp ((j₀).residueCharacter M.iota τ 1)
  rw [Source.RestrictedPlace.CM.residueCharacter_eq]

theorem exists_kernelData (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.GeometricConclusion R) :
    ∃ labels : (Fin M.s × Bool) ≃ Gal(E/ℚ),
      ∃ hlabels : ∀ (v : Fin M.s) (b : Bool),
        labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b),
        labels (⟨0, hM.1⟩, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E ∧
        ∀ a : M.Family, Nonempty (OrdinaryKernelConstruction.CM.PositiveData.KernelDataAt
          (AbelianScheme.FrobeniusKernel.CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a)
          j₀ M.iota hs₀ labels (M.s - 1) (PointsOrdinaryKernelData.CM.CMOrdinary.dimension_eq M hM)) := by
  obtain ⟨chosen, hc, hchosen, hlie⟩ := AbelianScheme.FrobeniusKernel.CMPointsFixedPoint.Construction.l45GeometricConclusion_fixedLieRanks M R hCMPoints
  obtain ⟨labels, hactive, hlabels, hmem, _⟩ := AbelianScheme.FrobeniusKernel.CMPointsModelLabels.Construction.exists_l45ModelLabels M hM chosen hc hchosen
  refine ⟨labels, hlabels, hactive, fun a => ?_⟩
  let D := AbelianScheme.FrobeniusKernel.CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a
  apply OrdinaryKernelConstruction.CM.PositiveData.construct D j₀ M.iota hs₀ labels
    (M.s - 1) (PointsOrdinaryKernelData.CM.CMOrdinary.dimension_eq M hM)
  · intro x v
    rw [Source.RestrictedPlace.CM.localCharacter_eq]
    exact AbelianScheme.FrobeniusKernel.CMPointsPointHeights.Construction.l45GeometricConclusion_fixedHeights M R hCMPoints a x.val (labels (v, false))
  · intro x
    have h := (hlie a x.val).1
    change AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (AbelianScheme.FrobeniusKernel.PointsGeometricPointData.Construction.l45FixedPointActionData M R a x.val).polarized.abelian
      (AbelianScheme.FrobeniusKernel.PointsGeometricPointData.Construction.l45FixedPointActionData M R a x.val).action
      (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j₀ M.iota (labels (⟨0, _⟩, false))) 1
    rw [hactive]
    exact (character_eq M j (PELModuli.CMPoints.Arithmetic.rationalConjugation E)) ▸ h
  · intro x v hv
    have hne : labels (v, false) ≠ PELModuli.CMPoints.Arithmetic.rationalConjugation E := by
      intro he
      have hi := labels.injective (he.trans hactive.symm)
      exact hv (congrArg (fun z : Fin M.s × Bool => z.1.val) hi)
    rcases (hlie a x.val).2 (labels (v, false)) (hmem v) hne with h | h
    · exact Or.inl ((character_eq M j (labels (v, false))) ▸ h)
    · exact Or.inr ((character_eq M j (labels (v, false))) ▸ h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedOrdinaryKernelData.CM.Ordinary
