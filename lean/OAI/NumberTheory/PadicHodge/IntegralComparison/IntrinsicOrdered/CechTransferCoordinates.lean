import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCechConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.RefinementMap

/-! # Cech Transfer Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechTransferCoordinates.Intrinsic

noncomputable section

/-! Original additive base-linear totals and generic ordered additive
totals give the same right/inverse-left resolution transfer. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (q : ℕ)

abbrev nativeTotal := Cech.ConcentrationNaturality.totalFunctor π U ⋙
  (CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)).mapHomologicalComplex (.up ℕ)
abbrev nativeFunctor := nativeTotal π U ⋙ homologyFunctor AddCommGrpCat.{u} (.up ℕ) q
abbrev genericFunctor := Additive.OrderedCechConcentration.functor U q

def iso (K : CochainComplex X.Modules ℕ) :=
  homologyMapIso (CechAdditiveCoordinates.Intrinsic.totalIso π U K) q

def transformation : nativeFunctor π U q ⟶ genericFunctor U q where
  app K := (iso π U q K).hom
  naturality _ _ a := by
    have h := congrArg (fun b => homologyMap b q)
      (CechAdditiveCoordinates.Intrinsic.totalIso_naturality π U a)
    simpa only [nativeFunctor, nativeTotal, genericFunctor,
      Additive.OrderedCechConcentration.functor, iso, Functor.comp_map,
      homologyFunctor_map, homologyMapIso_hom, homologyMap_comp] using h

variable {P K T : CochainComplex X.Modules ℕ}
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (T.X q).IsQuasicoherent]
  (l : K ⟶ T) [QuasiIso l] (a : P ⟶ T)

include hU in
theorem native_left_isIso : IsIso ((nativeFunctor π U q).map l) := by
  let : QuasiIso ((Cech.ConcentrationNaturality.totalFunctor π U).map l) :=
    OrderedCech.QuasiIso.quasiIso π U l hU
  let : QuasiIso ((nativeTotal π U).map l) := by
    change QuasiIso (((CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)).mapHomologicalComplex
      (.up ℕ)).map ((Cech.ConcentrationNaturality.totalFunctor π U).map l))
    infer_instance
  change IsIso (homologyMap ((nativeTotal π U).map l) q)
  infer_instance

include π hU in
theorem generic_left_isIso : IsIso ((genericFunctor U q).map l) := by
  let := CechAdditiveCoordinates.Intrinsic.quasiIso π U hU l
  change IsIso (homologyMap ((CechAdditiveCoordinates.Intrinsic.totalFunctor U).map l) q)
  infer_instance

def nativeMap := by
  letI := native_left_isIso π U hU q l
  exact IntegralComparison.Functor.RefinementMap.map (nativeFunctor π U q) l a

def genericMap := by
  letI := generic_left_isIso π U hU q l
  exact IntegralComparison.Functor.RefinementMap.map (genericFunctor U q) l a

theorem comparison : nativeMap π U hU q l a ≫ (iso π U q K).hom =
    (iso π U q P).hom ≫ genericMap π U hU q l a := by
  let := native_left_isIso π U hU q l
  let := generic_left_isIso π U hU q l
  exact IntegralComparison.Functor.RefinementMap.naturality (nativeFunctor π U q) (genericFunctor U q)
    (transformation π U q) l a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechTransferCoordinates.Intrinsic
