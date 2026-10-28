import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedOrdinaryKernelData
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ReductionLie

/-! # Fixed Ordinary Kernel Data -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedOrdinaryKernelData.Ordinary

noncomputable section

/-! Construct the full native ordinary kernel data with specified labels.
The integral PEL signature proves the compact ranks for every other pair,
so the labels need not be chosen again from CMPoints's representative set. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
  {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
  (hsplit : j.HasSplitCoordinates M.extendedEmbedding) (R : M.GoodIntegralReduction q j)
  (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ))
  (hlabels : ∀ (w : Fin M.s) (b : Bool),
    labels (w, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (w, b))
  (hactive : labels (⟨0, hM.1⟩, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E)

include hactive in
theorem fixed_labels_kernel_data (hgeom : AbelianScheme.FrobeniusKernel.CMPoints.Construction.GeometricConclusion R) (a : M.Family) :
    Nonempty (HeckeCycles.OrdinaryKernelConstruction.CM.PositiveData.KernelDataAt
      (AbelianScheme.FrobeniusKernel.CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a)
      (HeckeCycles.Source.RestrictedPlace.CM.choice M j) M.iota
      (HeckeCycles.Source.RestrictedPlace.CM.splitCoordinates M j hsplit) labels
      (M.s - 1) (HeckeCycles.PointsOrdinaryKernelData.CM.CMOrdinary.dimension_eq M hM)) := by
  let D := AbelianScheme.FrobeniusKernel.CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a
  apply HeckeCycles.OrdinaryKernelConstruction.CM.PositiveData.construct D (HeckeCycles.Source.RestrictedPlace.CM.choice M j)
    M.iota (HeckeCycles.Source.RestrictedPlace.CM.splitCoordinates M j hsplit) labels
    (M.s - 1) (HeckeCycles.PointsOrdinaryKernelData.CM.CMOrdinary.dimension_eq M hM)
  · intro x w
    rw [HeckeCycles.Source.RestrictedPlace.CM.localCharacter_eq]
    exact AbelianScheme.FrobeniusKernel.CMPointsPointHeights.Construction.l45GeometricConclusion_fixedHeights M R hgeom a x.val (labels (w, false))
  · intro x
    change AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (AbelianScheme.FrobeniusKernel.PointsGeometricPointData.Construction.l45FixedPointActionData M R a x.val).polarized.abelian
      (AbelianScheme.FrobeniusKernel.PointsGeometricPointData.Construction.l45FixedPointActionData M R a x.val).action
      (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter (HeckeCycles.Source.RestrictedPlace.CM.choice M j) M.iota
        (labels (⟨0, _⟩, false))) 1
    rw [hactive]
    exact (HeckeCycles.RestrictedOrdinaryKernelData.CM.Ordinary.character_eq M j (PELModuli.CMPoints.Arithmetic.rationalConjugation E)) ▸
      AbelianScheme.FrobeniusKernel.PointsPointLieRanks.Construction.l45FixedPoint_hasLieRank M R a x.val (PELModuli.CMPoints.Arithmetic.rationalConjugation E) 1
        (R.active_lieRank_one hM a _)
  · intro x w hw
    have hc : labels (w, false) ≠ PELModuli.CMPoints.Arithmetic.rationalConjugation E := by
      intro he
      have hi := labels.injective (he.trans hactive.symm)
      exact hw (congrArg (fun z : Fin M.s × Bool => z.1.val) hi)
    have hconj : PELModuli.CMPoints.Arithmetic.rationalConjugation E * PELModuli.CMPoints.Arithmetic.rationalConjugation E = 1 := by
      apply AlgEquiv.ext
      intro z
      exact NumberField.IsCMField.complexConj_apply_apply E z
    have hop : labels (⟨0, hM.1⟩, true) = 1 := by
      simpa only [Bool.not_false, hactive, hconj] using hlabels ⟨0, hM.1⟩ false
    have h1 : labels (w, false) ≠ 1 := by
      intro he
      exact Bool.false_ne_true (congrArg Prod.snd (labels.injective (he.trans hop.symm)))
    rcases R.compact_lieRank_zero_or_three hM a
      (AbelianScheme.FrobeniusKernel.PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x.val) (labels (w, false)) h1 hc with hz | hm
    · exact Or.inl ((HeckeCycles.RestrictedOrdinaryKernelData.CM.Ordinary.character_eq M j _) ▸
        AbelianScheme.FrobeniusKernel.PointsPointLieRanks.Construction.l45FixedPoint_hasLieRank M R a x.val _ 0 hz)
    · exact Or.inr ((HeckeCycles.RestrictedOrdinaryKernelData.CM.Ordinary.character_eq M j _) ▸
        AbelianScheme.FrobeniusKernel.PointsPointLieRanks.Construction.l45FixedPoint_hasLieRank M R a x.val _ 3 hm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedOrdinaryKernelData.Ordinary
