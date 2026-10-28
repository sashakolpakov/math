import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPadic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LinearMapEvaluation

/-! # Filled PEL -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledPEL.ParameterChoices

noncomputable section

/-! The original rational unitary matrix, filled by the identity in
the active pair, as an actual homomorphism to the original PEL group. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LinearMapEvaluation.TestTransport

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

def nativeFilledPEL : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b →* D.reference.FiniteSpecialUnitary :=
  (CM.AwayPELLevel.Approximation.cmAwayToPEL E D.reference hg.reference_admissible
    (CM.ActivePlace.Approximation.cmActivePlace E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)))).toMonoidHom.comp
      (CM.FiniteAway.Approximation.cmRationalFiniteAway E D.reference hg.reference_admissible
        (CM.ActivePlace.Approximation.cmActivePlace E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))))

def nativeFilledBlock (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b) (v : Fin s × Bool) :
    Matrix.SpecialLinearGroup (Fin 3) (Padic q) :=
  if v.1 = D.reference.distinguished then 1 else Matrix.SpecialLinearGroup.map (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) γ.val

theorem nativeFilledPEL_entry (hq : D.IsGoodCompletelySplitPrime)
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b) (v : Fin s × Bool) (i j : Fin 3) :
    Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v)
      ((nativeFilledPEL E D hg γ).val (Pi.single j 1) i) = (nativeFilledBlock E D γ v).val i j := by
  have h := AwayPadic.ParameterChoices.native_cmAwayToPEL_padic E D hg hq γ v i j
  exact h.trans (by unfold nativeFilledBlock; split_ifs <;> rfl)

theorem nativeFilledPEL_evaluate (hq : D.IsGoodCompletelySplitPrime)
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b) (v : Fin s × Bool) (x : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    (fun i => Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) ((nativeFilledPEL E D hg γ).val x i)) =
      (nativeFilledBlock E D γ v).val *ᵥ
        (fun i => Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) (x i)) := by
  have he := LinearMapEvaluation.TestTransport.linearMap_evaluate (Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v)).toRingHom
    (nativeFilledPEL E D hg γ).val.toLinearMap x
  have hm : (fun i j => Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v)
      ((nativeFilledPEL E D hg γ).val (Pi.single j 1) i)) = (nativeFilledBlock E D γ v).val := by
    funext i j
    exact nativeFilledPEL_entry E D hg hq γ v i j
  exact he.trans (congrArg (fun A : Matrix (Fin 3) (Fin 3) (Padic q) =>
    A *ᵥ (fun i => Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) (x i))) hm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledPEL.ParameterChoices
