import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentrationLocalRecovery

/-! # Additive Cech Refinement Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechRefinementConcentration

noncomputable section

/-! Forward cover refinement commutes with canonical additive concentration.
No cover quasi-isomorphism of the original complex is needed. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
variable {X : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
  (W : κ → X.Opens) (hW : ∀ i, IsAffineOpen (W i))
  (r : FormalCoproduct.mk κ W ⟶ FormalCoproduct.mk ι V)
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

@[reassoc]
theorem refinement_square (q : ℕ) :
    (AdditiveCechConcentration.iso U hU V hV K c hK q).hom ≫
      RelativeCech.Refinement.homology U V W r
        (AdditiveCechConcentration.coefficients ((single X.Modules (.up ℕ) c).obj (K.homology c))) q =
    RelativeCech.Refinement.homology U V W r (AdditiveCechConcentration.coefficients K) q ≫
      (AdditiveCechConcentration.iso U hU W hW K c hK q).hom := by
  let := AdditiveCechConcentration.projection_isIso U hU V hV K c hK q
  let := AdditiveCechConcentration.inclusion_isIso U hU V hV K c hK q
  let := AdditiveCechConcentration.projection_isIso U hU W hW K c hK q
  let := AdditiveCechConcentration.inclusion_isIso U hU W hW K c hK q
  exact ConcentrationLocalRecovery.square (AdditiveCechConcentration.functor U V q) (AdditiveCechConcentration.functor U W q) K c
    (RelativeCech.Refinement.homology U V W r (AdditiveCechConcentration.coefficients K) q)
    (RelativeCech.Refinement.homology U V W r (AdditiveCechConcentration.coefficients (CohomologyConcentration.truncation K c)) q)
    (RelativeCech.Refinement.homology U V W r
      (AdditiveCechConcentration.coefficients ((single X.Modules (.up ℕ) c).obj (K.homology c))) q)
    (RelativeCech.Refinement.homology_naturality U V W r (AdditiveCechConcentration.coefficientMap (CohomologyConcentration.projection K c)) q)
    (RelativeCech.Refinement.homology_naturality U V W r (AdditiveCechConcentration.coefficientMap (CohomologyConcentration.inclusion K c)) q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechRefinementConcentration
