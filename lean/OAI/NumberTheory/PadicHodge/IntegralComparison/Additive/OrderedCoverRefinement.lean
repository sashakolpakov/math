import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Refinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CoverRefinementQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.TotalQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCechConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.RefinementMap

/-! # Ordered Cover Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCoverRefinement

noncomputable section

/-! Full affine-cover refinement on the original additive ordered
Čech total, naturally for coefficient maps and canonical concentration. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} [X.IsSeparated]
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → X.Opens) (V : κ → X.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

abbrev map (K : CochainComplex X.Modules ℕ) :=
  OrderedCech.Refinement.totalMap U V r (Relative.AdditiveCechConcentration.coefficients K)

def transformation : IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.totalFunctor U ⟶
    IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.totalFunctor V :=
  Functor.whiskerLeft ((Relative.AdditiveCechConcentration.presheaves (X := X)).mapHomologicalComplex (.up ℕ))
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (OrderedCech.Refinement.transformation U V r) (.up ℕ))
      (HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ) (.up ℕ)))

omit [X.IsSeparated] in
theorem naturality {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) :
    (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.totalFunctor U).map a ≫ OrderedCoverRefinement.map U V r L =
      OrderedCoverRefinement.map U V r K ≫ (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.totalFunctor V).map a :=
  (transformation U V r).naturality a

abbrev homology (K : CochainComplex X.Modules ℕ) (q : ℕ) := homologyMap (OrderedCoverRefinement.map U V r K) q

def homologyTransformation (q : ℕ) :
    OrderedCechConcentration.functor U q ⟶
      OrderedCechConcentration.functor V q :=
  Functor.whiskerRight (transformation U V r) (homologyFunctor AddCommGrpCat.{u} (.up ℕ) q)

omit [X.IsSeparated] in
theorem homology_naturality {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) (q : ℕ) :
    (OrderedCechConcentration.functor U q).map a ≫ OrderedCoverRefinement.homology U V r L q =
      OrderedCoverRefinement.homology U V r K q ≫ (OrderedCechConcentration.functor V q).map a :=
  (homologyTransformation U V r q).naturality a

variable (hU : iSup U = ⊤) (hV : iSup V = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))

include hU hV haU haV in
theorem quasiIso (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent] :
    QuasiIso (OrderedCoverRefinement.map U V r K) := by
  apply TotalQuasiIso.quasiIso
  intro q
  let : QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (K.X q).presheaf) :=
    Open.CoverRefinementQuasiIso.Cech.quasiIso U V r (K.X q) ⊤ hU hV haU haV
  exact OrderedCech.Refinement.quasiIso U V r (K.X q).presheaf

include hU hV haU haV in
theorem homology_isIso (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent] (q : ℕ) :
    IsIso (OrderedCoverRefinement.homology U V r K q) := by
  let := quasiIso U V r hU hV haU haV K
  infer_instance

variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

theorem concentration (q : ℕ) :
    (OrderedCechConcentration.iso U haU K c hK q).hom ≫
      OrderedCoverRefinement.homology U V r ((single X.Modules (.up ℕ) c).obj (K.homology c)) q =
    OrderedCoverRefinement.homology U V r K q ≫
      (OrderedCechConcentration.iso V haV K c hK q).hom := by
  let := OrderedCechConcentration.projection_isIso U haU K c hK q
  let := OrderedCechConcentration.inclusion_isIso U haU K c hK q
  let := OrderedCechConcentration.projection_isIso V haV K c hK q
  let := OrderedCechConcentration.inclusion_isIso V haV K c hK q
  exact ConcentrationLocalRecovery.square
    (OrderedCechConcentration.functor U q)
    (OrderedCechConcentration.functor V q) K c _ _ _
    (homology_naturality U V r (CohomologyConcentration.projection K c) q)
    (homology_naturality U V r (CohomologyConcentration.inclusion K c) q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCoverRefinement
