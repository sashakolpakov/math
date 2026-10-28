import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.SquareBaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

/-! # Square Normalization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.SquareNormalization

noncomputable section

/-!
# The canonical open-square mate is the standard geometric pullback path
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry

section

/-- The uniqueness isomorphism between two left adjoints has identity right mate. -/
theorem leftAdjointUniq_hom_mate {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R) :
    conjugateEquiv b a (a.leftAdjointUniq b).hom = 𝟙 R := by
  change (conjugateEquiv b a) ((conjugateEquiv b a).symm (𝟙 R)) = _
  exact (conjugateEquiv b a).apply_symm_apply _

/-- The inverse uniqueness isomorphism has identity right mate as well. -/
theorem leftAdjointUniq_inv_mate {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R) :
    conjugateEquiv a b (a.leftAdjointUniq b).inv = 𝟙 R := by
  change (conjugateEquiv a b) ((conjugateEquiv a b).symm (𝟙 R)) = _
  exact (conjugateEquiv a b).apply_symm_apply _

end

universe u

/-- The actual restriction-to-pullback comparison has identity mate. -/
theorem restrictIso_hom_mate {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction i) (Scheme.Modules.restrictAdjunction i)
      (Scheme.Modules.restrictFunctorIsoPullback i).hom = 𝟙 (Scheme.Modules.pushforward i) :=
  leftAdjointUniq_hom_mate (Scheme.Modules.restrictAdjunction i)
    (Scheme.Modules.pullbackPushforwardAdjunction i)

/-- The inverse actual open restriction comparison also has identity mate. -/
theorem restrictIso_inv_mate {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] :
    conjugateEquiv (Scheme.Modules.restrictAdjunction i) (Scheme.Modules.pullbackPushforwardAdjunction i)
      (Scheme.Modules.restrictFunctorIsoPullback i).inv = 𝟙 (Scheme.Modules.pushforward i) :=
  leftAdjointUniq_inv_mate (Scheme.Modules.restrictAdjunction i)
    (Scheme.Modules.pullbackPushforwardAdjunction i)

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) [IsOpenImmersion iX] [IsOpenImmersion iY]
  (h : iX ≫ f = f' ≫ iY)

/-- The standard path uses open restriction comparisons and actual scheme pullback compositions. -/
def standardSquare :
    Scheme.Modules.restrictFunctor iY ⋙ Scheme.Modules.pullback f' ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor iX :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback iY) (Scheme.Modules.pullback f') ≪≫
    Scheme.Modules.pullbackComp f' iY ≪≫ (Scheme.Modules.pullbackCongr h).symm ≪≫
    (Scheme.Modules.pullbackComp iX f).symm ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback f) (Scheme.Modules.restrictFunctorIsoPullback iX).symm

/-- The standard geometric path has precisely the actual direct-image square as its mate. -/
theorem standardSquare_mate :
    conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (Scheme.Modules.restrictAdjunction iX))
      ((Scheme.Modules.restrictAdjunction iY).comp (Scheme.Modules.pullbackPushforwardAdjunction f'))
      (standardSquare f f' iX iY h).hom = (SquareBaseChange.directImageSquare f f' iX iY h).hom := by
  change conjugateEquiv _ _
    (Functor.whiskerRight (Scheme.Modules.restrictFunctorIsoPullback iY).hom (Scheme.Modules.pullback f') ≫
      (Scheme.Modules.pullbackComp f' iY).hom ≫ (Scheme.Modules.pullbackCongr h).inv ≫
      (Scheme.Modules.pullbackComp iX f).inv ≫
      Functor.whiskerLeft (Scheme.Modules.pullback f) (Scheme.Modules.restrictFunctorIsoPullback iX).inv) = _
  rw [← conjugateEquiv_comp _ ((Scheme.Modules.pullbackPushforwardAdjunction iY).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f')),
    ← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (f' ≫ iY)),
    ← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (iX ≫ f)),
    ← conjugateEquiv_comp _ ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction iX)),
    conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    restrictIso_inv_mate, restrictIso_hom_mate,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    Affine.Composition.pullbackCongr_mate, Cech.MateNormalization.conjugate_pullbackComp_hom]
  exact Category.assoc _ _ _

/-- The adjunction-defined square is exactly the standard geometric pullback square. -/
theorem leftSquare_eq_standard :
    SquareBaseChange.leftSquare f f' iX iY h = standardSquare f f' iX iY h := by
  apply Iso.ext
  apply (conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (Scheme.Modules.restrictAdjunction iX))
    ((Scheme.Modules.restrictAdjunction iY).comp (Scheme.Modules.pullbackPushforwardAdjunction f'))).injective
  change (conjugateEquiv _ _) ((conjugateEquiv _ _).symm
    (SquareBaseChange.directImageSquare f f' iX iY h).hom) = _
  rw [Equiv.apply_symm_apply]
  exact (standardSquare_mate f f' iX iY h).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.SquareNormalization
