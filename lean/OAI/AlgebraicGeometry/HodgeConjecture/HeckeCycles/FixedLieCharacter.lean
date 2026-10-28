import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsPointLieRanks
import OAI.RepresentationTheory.Hecke.CoefficientResidueSquare

/-! # Fixed Lie Character -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FixedLieCharacter.CM

noncomputable section

/-! The character in the full CMPoints geometric conclusion is the original
coefficient block's characteristic-q Lie character. -/

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsPointLieRanks.Construction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K) {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)

theorem character_eq (τ : Gal(E/ℚ)) : AbelianScheme.FrobeniusKernel.PointsPointLieRanks.Construction.l45FixedLieCharacter M (j := j) τ =
    RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter (k := AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) j M.extendedEmbedding τ := by
  have h : (algebraMap (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)).comp PadicInt.toZMod =
      (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockResidueCast (k := AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) (q := q)).comp (PadicInt.toZModPow 1) :=
    RepresentationTheory.Hecke.CoefficientResidueSquare.OrdinaryCharacterIntrinsic.padic_residue_hom_unique _ _
  exact congrArg (fun f : ℤ_[q] →+* AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q => f.comp (j.localCharacter M.extendedEmbedding τ)) h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FixedLieCharacter.CM
