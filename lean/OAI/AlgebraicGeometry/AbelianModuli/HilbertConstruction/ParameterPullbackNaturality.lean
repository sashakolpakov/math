import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ParameterFunctoriality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OverIsoNaturality

/-! # Parameter Pullback Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackNaturality

noncomputable section

/-! The geometric comparison between single and iterated parameter pullbacks is a natural isomorphism of functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {U T : Over S} (c : U ⟶ T)

theorem singleParameterBaseChangeMap_natural {A B : Over S} (f : A ⟶ B) :
    ((Over.pullback U.hom).map f).left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap c B =
      Single.ParameterBaseChange.singleParameterBaseChangeMap c A ≫ ((Over.pullback T.hom).map f).left := by
  apply (IsPullback.of_hasPullback B.hom T.hom).hom_ext
  · have hT : ((Over.pullback T.hom).map f).left ≫ pullback.fst B.hom T.hom =
        pullback.fst A.hom T.hom ≫ f.left := pullback.lift_fst _ _ _
    rw [Category.assoc, Single.ParameterBaseChange.singleParameterBaseChangeMap_comp, Category.assoc, hT,
      ← Category.assoc, Single.ParameterBaseChange.singleParameterBaseChangeMap_comp]
    exact pullback.lift_fst _ _ _
  · change (((Over.pullback U.hom).map f).left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap c B) ≫
        ((Over.pullback T.hom).obj B).hom =
      (Single.ParameterBaseChange.singleParameterBaseChangeMap c A ≫ ((Over.pullback T.hom).map f).left) ≫
        ((Over.pullback T.hom).obj B).hom
    rw [Category.assoc, Single.ParameterFunctoriality.singleParameterBaseChangeMap_over, ← Category.assoc,
      ((Over.pullback U.hom).map f).w, Category.assoc, ((Over.pullback T.hom).map f).w,
      Single.ParameterFunctoriality.singleParameterBaseChangeMap_over]

theorem singleParameterBaseChangeIso_natural {A B : Over S} (f : A ⟶ B) :
    ((Over.pullback U.hom).map f) ≫ (Single.ParameterBaseChange.singleParameterBaseChangeIso c B).hom =
      (Single.ParameterBaseChange.singleParameterBaseChangeIso c A).hom ≫ (Over.pullback c.left).map ((Over.pullback T.hom).map f) :=
  (Cartesian.OverIsoNaturality.cartesianAmbientOverIso_natural c.left (Single.ParameterBaseChange.singleParameterBaseChangeMap c A)
    (Single.ParameterBaseChange.singleParameterBaseChangeMap c B) (Single.ParameterBaseChange.singleParameterBaseChangeMap_isPullback c A)
    (Single.ParameterBaseChange.singleParameterBaseChangeMap_isPullback c B) ((Over.pullback U.hom).map f)
    ((Over.pullback T.hom).map f) (singleParameterBaseChangeMap_natural c f).symm).symm

def singleParameterBaseChangeNatIso :
    Over.pullback U.hom ≅ Over.pullback T.hom ⋙ Over.pullback c.left :=
  NatIso.ofComponents (Single.ParameterBaseChange.singleParameterBaseChangeIso c) (fun f => singleParameterBaseChangeIso_natural c f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackNaturality
