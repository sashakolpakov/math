import OAI.AlgebraicGeometry.PELModuli.CMPoints.EmptyCoefficientBase
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Morphisms
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons

/-! # Fixed Coefficient Models -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedCoefficientModels

noncomputable section

/-! Fixed integral models at finite coefficient stages. All comparisons
retain their actual projections to the supplied original models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R F : Type} [CommRing R] [Field F] [Algebra R F]
  (X : Over (Spec (.of R)))
  {G : Over (Spec (.of F))} (p : G.left ⟶ X.left)
  (hp : IsPullback p G.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R F))))

def fixedCoefficientProjection (s : Finset F) :
    G.left ⟶ ((Over.pullback (EmptyCoefficientBase.coefficientStructureMap s)).obj X).left :=
  pullback.lift p (G.hom ≫ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R F s) (by
    rw [Category.assoc, EmptyCoefficientBase.genericBaseMap_structure]
    exact hp.w)

@[reassoc]
theorem fixedCoefficientProjection_fst (s : Finset F) :
    fixedCoefficientProjection X p hp s ≫ pullback.fst X.hom (EmptyCoefficientBase.coefficientStructureMap s) = p :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem fixedCoefficientProjection_snd (s : Finset F) :
    fixedCoefficientProjection X p hp s ≫ pullback.snd X.hom (EmptyCoefficientBase.coefficientStructureMap s) =
      G.hom ≫ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R F s :=
  pullback.lift_snd _ _ _

theorem fixedCoefficientProjection_cartesian (s : Finset F) :
    IsPullback (fixedCoefficientProjection X p hp s) G.hom
      ((Over.pullback (EmptyCoefficientBase.coefficientStructureMap s)).obj X).hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R F s) := by
  apply IsPullback.of_right ?_ (fixedCoefficientProjection_snd X p hp s)
    (IsPullback.of_hasPullback X.hom (EmptyCoefficientBase.coefficientStructureMap s))
  rw [fixedCoefficientProjection_fst, EmptyCoefficientBase.genericBaseMap_structure]
  exact hp

theorem fixedCoefficientModel_finitePresentation (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (s : Finset F) :
    ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism ((Over.pullback (EmptyCoefficientBase.coefficientStructureMap s)).obj X).hom := by
  let : LocallyOfFinitePresentation X.hom := hX.1
  let : QuasiCompact X.hom := hX.2.1
  let : QuasiSeparated X.hom := hX.2.2
  change ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (pullback.snd X.hom _)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

def fixedCoefficientEnlargementIso {s t : Finset F} (h : s ⊆ t) :
    (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R F h)).obj
      ((Over.pullback (EmptyCoefficientBase.coefficientStructureMap s)).obj X) ≅
        (Over.pullback (EmptyCoefficientBase.coefficientStructureMap t)).obj X :=
  IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X (EmptyCoefficientBase.coefficientStructureMap s)
    (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R F h) (EmptyCoefficientBase.coefficientStructureMap t) (EmptyCoefficientBase.coefficientBaseMap_structure h)

theorem fixedCoefficientEnlargementIso_fst {s t : Finset F} (h : s ⊆ t) :
    (fixedCoefficientEnlargementIso X h).hom.left ≫
        pullback.fst X.hom (EmptyCoefficientBase.coefficientStructureMap t) =
      pullback.fst (pullback.snd X.hom (EmptyCoefficientBase.coefficientStructureMap s)) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R F h) ≫
        pullback.fst X.hom (EmptyCoefficientBase.coefficientStructureMap s) :=
  IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_fst X _ _ _ _

theorem fixedCoefficientProjection_enlarge {s t : Finset F} (h : s ⊆ t) :
    IntegralModel.Coefficient.Morphisms.Coefficients.genericModelLift
        ((Over.pullback (EmptyCoefficientBase.coefficientStructureMap s)).obj X)
        (fixedCoefficientProjection X p hp s)
        (fixedCoefficientProjection_cartesian X p hp s).w h ≫
      (fixedCoefficientEnlargementIso X h).hom.left = fixedCoefficientProjection X p hp t := by
  apply pullback.hom_ext
  · rw [Category.assoc, fixedCoefficientEnlargementIso_fst, ← Category.assoc]
    exact (congrArg (fun f => f ≫ pullback.fst X.hom (EmptyCoefficientBase.coefficientStructureMap s))
      (IntegralModel.Coefficient.Morphisms.Coefficients.genericModelLift_fst _ _
        (fixedCoefficientProjection_cartesian X p hp s).w h)).trans
      ((fixedCoefficientProjection_fst X p hp s).trans
        (fixedCoefficientProjection_fst X p hp t).symm)
  · rw [Category.assoc]
    change _ ≫ ((fixedCoefficientEnlargementIso X h).hom.left ≫
      ((Over.pullback (EmptyCoefficientBase.coefficientStructureMap t)).obj X).hom) = _
    rw [(fixedCoefficientEnlargementIso X h).hom.w]
    exact (IntegralModel.Coefficient.Morphisms.Coefficients.genericModelLift_snd _ _
      (fixedCoefficientProjection_cartesian X p hp s).w h).trans
      (fixedCoefficientProjection_snd X p hp t).symm

theorem fixedCoefficientProjection_enlarge_inv {s t : Finset F} (h : s ⊆ t) :
    fixedCoefficientProjection X p hp t ≫ (fixedCoefficientEnlargementIso X h).inv.left =
      IntegralModel.Coefficient.Morphisms.Coefficients.genericModelLift
        ((Over.pullback (EmptyCoefficientBase.coefficientStructureMap s)).obj X)
        (fixedCoefficientProjection X p hp s)
        (fixedCoefficientProjection_cartesian X p hp s).w h := by
  exact (((Over.forget _).mapIso (fixedCoefficientEnlargementIso X h)).eq_comp_inv.mpr
    (fixedCoefficientProjection_enlarge X p hp h)).symm

/-- Foundations extends a morphism while retaining both specified original models. -/
theorem morphism_between_fixed_coefficient_models_descends
    {Y : Over (Spec (.of R))} {H : Over (Spec (.of F))}
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (pY : H.left ⟶ Y.left)
    (hpY : IsPullback pY H.hom Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R F))))
    (a : G ⟶ H) :
    ∃ (t : Finset F)
      (b : (Over.pullback (EmptyCoefficientBase.coefficientStructureMap t)).obj X ⟶
        (Over.pullback (EmptyCoefficientBase.coefficientStructureMap t)).obj Y),
      fixedCoefficientProjection X p hp t ≫ b.left =
        a.left ≫ fixedCoefficientProjection Y pY hpY t := by
  let X₀ := (Over.pullback (EmptyCoefficientBase.coefficientStructureMap (R := R) (F := F) ∅)).obj X
  let Y₀ := (Over.pullback (EmptyCoefficientBase.coefficientStructureMap (R := R) (F := F) ∅)).obj Y
  obtain ⟨t, h, b, hb⟩ := IntegralModel.Coefficient.Morphisms.Coefficients.morphism_between_models_descends X₀ Y₀
    (fixedCoefficientModel_finitePresentation X hX ∅)
    (fixedCoefficientModel_finitePresentation Y hY ∅)
    (fixedCoefficientProjection X p hp ∅) (fixedCoefficientProjection Y pY hpY ∅)
    (fixedCoefficientProjection_cartesian X p hp ∅)
    (fixedCoefficientProjection_cartesian Y pY hpY ∅) a
  refine ⟨t, (fixedCoefficientEnlargementIso X h).inv ≫ b ≫
    (fixedCoefficientEnlargementIso Y h).hom, ?_⟩
  change fixedCoefficientProjection X p hp t ≫
      ((fixedCoefficientEnlargementIso X h).inv.left ≫
        (b.left ≫ (fixedCoefficientEnlargementIso Y h).hom.left)) = _
  rw [← Category.assoc, fixedCoefficientProjection_enlarge_inv,
    ← Category.assoc, hb, Category.assoc, fixedCoefficientProjection_enlarge]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedCoefficientModels
