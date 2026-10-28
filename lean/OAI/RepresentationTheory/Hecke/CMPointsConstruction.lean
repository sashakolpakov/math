import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryReduction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPoints

/-! # CM Points Construction -/

namespace OAI.RepresentationTheory.Hecke.CMPointsConstruction.OrdinaryCharacterIntrinsic

/-! Supply the complete ordinary-reduction proposition from its openness,
splitting, Hilbert-Hom, and endomorphism-equation inputs. -/

universe u v

theorem provedCMPointsInput
    (hOpenness : AlgebraicGeometry.PELModuli.CMPoints.OrdinaryReduction.OpennessInput) (hSplitPrimes : AlgebraicGeometry.PELModuli.CMPoints.Arithmetic.SplitPrimesInput)
    (hHilb : AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0}) :
    AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput :=
  AlgebraicGeometry.PELModuli.CMPoints.OrdinaryReduction.exists_completely_split_prime_dense_ordinary hOpenness hSplitPrimes hHilb hEnd

end OAI.RepresentationTheory.Hecke.CMPointsConstruction.OrdinaryCharacterIntrinsic
