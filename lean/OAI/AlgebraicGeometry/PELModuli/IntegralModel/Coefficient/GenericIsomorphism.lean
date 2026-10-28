import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Isomorphisms
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons

/-! # Generic Isomorphism -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GenericIsomorphism.Coefficients

noncomputable section

/-! An actual morphism of finite-presentation coefficient models that
is an isomorphism on the generic fiber becomes an isomorphism after
enlarging the finite coefficient ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem coefficient_generic_isIso_after_two_enlargements
    {R K : Type} [CommRing R] [Field K] [Algebra R K] {s : Finset K}
    (X Y : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s))
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (f : X ⟶ Y) [IsIso ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).map f)] :
    ∃ (t : Finset K) (hst : s ⊆ t) (z : Finset K) (htz : t ⊆ z),
      IsIso ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz)).map
        ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)).map f)) := by
  let g := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s
  let Xg := (Over.pullback g).obj X
  let Yg := (Over.pullback g).obj Y
  let px := pullback.fst X.hom g
  let py := pullback.fst Y.hom g
  let hx : IsPullback px Xg.hom X.hom g := IsPullback.of_hasPullback _ _
  let hy : IsPullback py Yg.hom Y.hom g := IsPullback.of_hasPullback _ _
  obtain ⟨t, hst, e, he⟩ := Isomorphisms.Coefficients.isomorphism_between_models_descends X Y hX hY px py hx hy
    (asIso ((Over.pullback g).map f))
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
  let px' := Morphisms.Coefficients.genericModelLift (X := Xg) X px hx.w hst
  let py' := Morphisms.Coefficients.genericModelLift (X := Yg) Y py hy.w hst
  have hp : px' ≫ (F.map f).left = ((Over.pullback g).map f).left ≫ py' :=
    BaseChange.Coefficients.genericModelLift_map (X := Xg) (Y := Yg) X Y px py hx.w hy.w ((Over.pullback g).map f) f
      (pullback.lift_fst _ _ _).symm hst
  have hEq : px' ≫ (F.map f).left = px' ≫ e.hom.left := hp.trans he.symm
  obtain ⟨z, htz, hz⟩ := Morphisms.Coefficients.equation_between_models_descends (F.obj X) (F.obj Y)
    (Finiteness.Coefficients.baseChange_finitePresentation _ X hX) (Finiteness.Coefficients.baseChange_finitePresentation _ Y hY)
    px' (Morphisms.Coefficients.genericModelLift_cartesian (X := Xg) X px hx hst) (F.map f) e.hom hEq
  have hmap : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz)).map (F.map f) =
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz)).map e.hom :=
    FiniteEquations.Coefficients.baseChange_map_eq_of_fst_eq _ _ _ _ _ hz
  refine ⟨t, hst, z, htz, ?_⟩
  rw [hmap]
  infer_instance

theorem coefficient_generic_isIso_after_enlargement
    {R K : Type} [CommRing R] [Field K] [Algebra R K] {s : Finset K}
    (X Y : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s))
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (f : X ⟶ Y) [IsIso ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).map f)] :
    ∃ (t : Finset K) (hst : s ⊆ t), IsIso ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)).map f) := by
  obtain ⟨t, hst, z, htz, hi⟩ := coefficient_generic_isIso_after_two_enlargements X Y hX hY f
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
  let G := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz)
  let H := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K (hst.trans htz))
  let e := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
    (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K (hst.trans htz))
    (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap_comp R K hst htz)
  have hn : G.map (F.map f) ≫ (e.app Y).hom = (e.app X).hom ≫ H.map f := e.hom.naturality f
  have he : H.map f = (e.app X).inv ≫ G.map (F.map f) ≫ (e.app Y).hom := by
    rw [hn, Iso.inv_hom_id_assoc]
  refine ⟨z, hst.trans htz, ?_⟩
  change IsIso (H.map f)
  rw [he]
  infer_instance

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GenericIsomorphism.Coefficients
