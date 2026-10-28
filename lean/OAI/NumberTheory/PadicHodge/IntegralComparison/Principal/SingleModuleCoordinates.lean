import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SinglePresheafCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.SingleCoefficientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.MappedSingleCoordinates

/-! # Single Module Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleModuleCoordinates

noncomputable section

/-! The original principal single coordinates factor through the actual
single map of the principal module functor, scalar restriction, and the
original augmented single-total coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) (c : ℕ) {ι : Type u} [LinearOrder ι]
  (W : ι → SectionPresheaf.Index U)

local instance finiteBiproducts : HasFiniteBiproducts (ModuleCat.{u} Γ(X, U)) :=
  Abelian.hasFiniteBiproducts

abbrev moduleFunctor := ModuleFunctor.functor U hU
abbrev additiveFunctor := AdditiveSections.additiveFunctor U hU
abbrev forgetScalars := AdditiveSections.forgetScalars U

def coefficientIso (g : ℕ) :=
  AugmentedCech.SingleCoefficientCoordinates.coefficientIso W
    (moduleFunctor U hU) (forgetScalars U) N g ≪≫
      homologyMapIso ((AugmentedOrdered.CechFunctor.functor W).mapIso
        ((AdditiveSections.functorIso U hU).app N)) g

abbrev singleMap := HomologicalComplex₂.total.map
  (((AugmentedOrdered.CechFunctor.functor W).mapHomologicalComplex (.up ℕ)).map
    ((singleMapHomologicalComplex (moduleFunctor U hU) (.up ℕ) c).hom.app N)) (.up ℕ)

def moduleCoordinates (g q : ℕ) (hq : q = g+c) :=
  eqToIso (congrArg (fun j =>
    ((IntegralComparison.Functor.SingleTotal.bicomplex (AugmentedOrdered.CechFunctor.functor W)
      ((moduleFunctor U hU).obj N) c).total (.up ℕ)).homology j) hq) ≪≫
    IntegralComparison.Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor W)
      ((moduleFunctor U hU).obj N) c g

private theorem original (g : ℕ) :
    (SinglePresheafCoordinates.coordinates U hU N c W g (g+c) rfl).hom =
      (AdditiveSections.homologyIso U hU
        ((single X.Modules (.up ℕ) c).obj N) W (g+c)).hom ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso
        (additiveFunctor U hU ⋙ AugmentedOrdered.CechFunctor.functor W) N c g).hom := by
  simp only [SinglePresheafCoordinates.coordinates,
    PresheafSingleIndexedCoordinates.sourceIso,
    eqToIso_refl, Iso.refl_trans, Iso.trans_hom]
  rw [← SinglePresheafCoordinates.factor, Category.assoc]
  congr 1
  exact Reference.SinglePresheafCoordinates.coordinates N c
    (Cech.SingleFunctorCoordinates.localFunctor
      (AdditiveSections.opens U hU) W) g

private theorem scalar_coordinates (g : ℕ) :
    (AdditiveSections.homologyIso U hU
      ((single X.Modules (.up ℕ) c).obj N) W (g+c)).hom ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso
        (additiveFunctor U hU ⋙ AugmentedOrdered.CechFunctor.functor W) N c g).hom =
    (forgetScalars U).map (IntegralComparison.Functor.SingleTotal.homologyIso
      (moduleFunctor U hU ⋙ AugmentedOrdered.CechFunctor.functor W) N c g).hom ≫
      (coefficientIso U hU N W g).hom := by
  let H := AugmentedCech.SingleCoefficientCoordinates.targetFunctor W
    (moduleFunctor U hU) (forgetScalars U)
  let K := additiveFunctor U hU ⋙ AugmentedOrdered.CechFunctor.functor W
  let e : H ≅ K := Functor.isoWhiskerRight
    (AdditiveSections.functorIso U hU) (AugmentedOrdered.CechFunctor.functor W)
  have he := IntegralComparison.Functor.SingleMapCoordinates.naturality H K e.hom N c g
  simp only [AdditiveSections.homologyIso,
    AdditiveSections.totalIso, Iso.trans_hom,
    homologyMapIso_hom, homologyMap_comp, Category.assoc]
  erw [he]
  change (AugmentedCech.CoefficientTotal.homologyIso W (forgetScalars U)
    (((moduleFunctor U hU).mapHomologicalComplex (.up ℕ)).obj
      ((single X.Modules (.up ℕ) c).obj N)) (g+c)).hom ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso H N c g).hom ≫
        homologyMap (e.hom.app N) g = _
  erw [← Category.assoc,
    AugmentedCech.SingleCoefficientCoordinates.comparison W (moduleFunctor U hU)
      (forgetScalars U) N c g, Category.assoc]

theorem factor (g q : ℕ) (hq : q = g+c) :
    (SinglePresheafCoordinates.coordinates U hU N c W g q hq).hom =
      (forgetScalars U).map (homologyMap (singleMap U hU N c W) q) ≫
        (forgetScalars U).map (moduleCoordinates U hU N c W g q hq).hom ≫
          (coefficientIso U hU N W g).hom := by
  subst q
  rw [original, scalar_coordinates]
  simp only [moduleCoordinates, eqToIso_refl, Iso.refl_trans]
  rw [← Category.assoc, ← Functor.map_comp]
  congr 1
  exact congrArg (fun a => (forgetScalars U).map a)
    (IntegralComparison.Functor.MappedSingleCoordinates.comparison (moduleFunctor U hU)
      (AugmentedOrdered.CechFunctor.functor W) N c g).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleModuleCoordinates
