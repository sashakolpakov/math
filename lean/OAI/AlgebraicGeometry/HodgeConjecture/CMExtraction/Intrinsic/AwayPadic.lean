import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AwayPadic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PlaceFibers

/-! # Away Padic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPadic.ParameterChoices

noncomputable section

/-! At q the literal filled PEL away element is the identity in the
active conjugate pair and the original rational matrix in every other slot. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AwayPadic.Approximation

theorem equal_conditional {A : Type*} (p : Prop) [Decidable p] {x a b : A}
    (hp : p → x = a) (hn : ¬p → x = b) : x = if p then a else b := by
  by_cases h : p
  · exact (hp h).trans (ite_eq_left h).symm
  · exact (hn h).trans (ite_eq_right h).symm

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)

include hq in
theorem native_cmAwayToPEL_padic (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b)
    (v : Fin s × Bool) (i j : Fin 3) :
    Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v)
      ((CM.AwayPELLevel.Approximation.cmAwayToPEL E D.reference hg.reference_admissible
        (CM.ActivePlace.Approximation.cmActivePlace E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)))
        (CM.FiniteAway.Approximation.cmRationalFiniteAway E D.reference hg.reference_admissible
          (CM.ActivePlace.Approximation.cmActivePlace E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))) γ)).val
            (Pi.single j 1) i) =
      if v.1 = D.reference.distinguished then (1 : Matrix (Fin 3) (Fin 3) (Padic q)) i j
      else LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v (γ.val.val i j) := by
  exact equal_conditional (v.1 = D.reference.distinguished)
    (fun hv => CM.AwayPadic.Approximation.cmAwayToPEL_padic_same E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) D.reference hg.reference_admissible _
      ((PlaceFibers.ParameterChoices.native_cmActivePlace_fiber E D hg hq v (D.reference.distinguished, false)).mpr hv) _ i j)
    (fun hv => CM.AwayPadic.Approximation.cmAwayToPEL_padic_rational_other E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) D.reference hg.reference_admissible _
      (fun h => hv ((PlaceFibers.ParameterChoices.native_cmActivePlace_fiber E D hg hq v (D.reference.distinguished, false)).mp h)) γ i j)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPadic.ParameterChoices
