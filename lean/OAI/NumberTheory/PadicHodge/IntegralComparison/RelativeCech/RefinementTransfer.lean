import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.RefinementMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechGlobalConcentration

/-! # Refinement Transfer -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.RefinementTransfer

noncomputable section

/-! Both original resolution maps are retained by relative Čech
refinement and by global extension, including inverse left maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
  (W : κ → X.Opens) (hW : ∀ i, IsAffineOpen (W i))
  (r : FormalCoproduct.mk κ W ⟶ FormalCoproduct.mk ι V) (q : ℕ)

def refinement : Relative.AdditiveCechConcentration.functor U V q ⟶ Relative.AdditiveCechConcentration.functor U W q where
  app K := Refinement.homology U V W r (Relative.AdditiveCechConcentration.coefficients K) q
  naturality _ _ a := Refinement.homology_naturality U V W r (Relative.AdditiveCechConcentration.coefficientMap a) q

def extension : Relative.AdditiveCechConcentration.functor U V q ⟶ Relative.AdditiveCechGlobalConcentration.SupportedPureClass.globalFunctor U V q where
  app K := Relative.AdditiveCechGlobalConcentration.SupportedPureClass.extension U V K q
  naturality _ _ a := Relative.AdditiveCechGlobalConcentration.SupportedPureClass.extension_naturality U V a q

variable {P K T : CochainComplex X.Modules ℕ}
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (T.X q).IsQuasicoherent]
  (l : K ⟶ T) [QuasiIso l] (a : P ⟶ T)

include hU hV in
theorem left_isIso : IsIso ((Relative.AdditiveCechConcentration.functor U V q).map l) := by
  let := Relative.AdditiveCechConcentration.quasiIso U hU V hV l
  change IsIso (homologyMap ((Relative.AdditiveCechConcentration.totalFunctor U V).map l) q)
  infer_instance

include hU hV in
theorem global_left_isIso : IsIso ((Relative.AdditiveCechGlobalConcentration.SupportedPureClass.globalFunctor U V q).map l) := by
  let := IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.quasiIso (𝟙 X)
    (Intersections.cover U V)
    (ConcentrationNaturality.cover_affine U hU V hV) l
  change IsIso (homologyMap
    ((IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.totalFunctor (Intersections.cover U V)).map l) q)
  infer_instance

def map := by
  letI := left_isIso U hU V hV q l
  exact Functor.RefinementMap.map (Relative.AdditiveCechConcentration.functor U V q) l a

def globalMap := by
  letI := global_left_isIso U hU V hV q l
  exact Functor.RefinementMap.map (Relative.AdditiveCechGlobalConcentration.SupportedPureClass.globalFunctor U V q) l a

theorem refinement_square : RefinementTransfer.map U hU V hV q l a ≫ (refinement U V W r q).app K =
    (refinement U V W r q).app P ≫ RefinementTransfer.map U hU W hW q l a := by
  let := left_isIso U hU V hV q l
  let := left_isIso U hU W hW q l
  exact Functor.RefinementMap.naturality (Relative.AdditiveCechConcentration.functor U V q) (Relative.AdditiveCechConcentration.functor U W q)
    (refinement U V W r q) l a

theorem extension_square : RefinementTransfer.map U hU V hV q l a ≫ (extension U V q).app K =
    (extension U V q).app P ≫ globalMap U hU V hV q l a := by
  let := left_isIso U hU V hV q l
  let := global_left_isIso U hU V hV q l
  exact Functor.RefinementMap.naturality (Relative.AdditiveCechConcentration.functor U V q)
    (Relative.AdditiveCechGlobalConcentration.SupportedPureClass.globalFunctor U V q) (extension U V q) l a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.RefinementTransfer
