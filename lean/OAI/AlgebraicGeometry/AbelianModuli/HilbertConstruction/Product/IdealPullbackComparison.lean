import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdentityParameterIdealRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ConditionIdeals

/-! # Ideal Pullback Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.IdealPullbackComparison

noncomputable section

/-! Vanishing on the over-category product is equivalent to vanishing on the actual scheme pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def overProductPullbackIso {S : Scheme.{u}} (X T : Over S) :
    (T ⨯ X).left ≅ pullback X.hom T.hom :=
  Over.prodLeftIsoPullback T X ≪≫ pullbackSymmetry T.hom X.hom

theorem overProductPullbackIso_hom_fst {S : Scheme.{u}} (X T : Over S) :
    (overProductPullbackIso X T).hom ≫ pullback.fst X.hom T.hom = IdentityParameterIdealRecovery.overProductSourceMap X T := by
  change ((Over.prodLeftIsoPullback T X).hom ≫ (pullbackSymmetry T.hom X.hom).hom) ≫
    pullback.fst X.hom T.hom = (prod.snd : T ⨯ X ⟶ X).left
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst, Over.prodLeftIsoPullback_hom_snd]

theorem overProduct_ideal_zero_iff_pullback {S : Scheme.{u}} (X T : Over S) (I : X.left.IdealSheafData) :
    I.comap (IdentityParameterIdealRecovery.overProductSourceMap X T) = ⊥ ↔ I.comap (pullback.fst X.hom T.hom) = ⊥ := by
  rw [Closed.ConditionIdeals.ideal_comap_eq_bot_iff, Closed.ConditionIdeals.ideal_comap_eq_bot_iff]
  have hk : (IdentityParameterIdealRecovery.overProductSourceMap X T).ker = (pullback.fst X.hom T.hom).ker :=
    (congrArg Scheme.Hom.ker (overProductPullbackIso_hom_fst X T)).symm.trans
      (Scheme.Hom.ker_comp_of_isIso (overProductPullbackIso X T).hom (pullback.fst X.hom T.hom))
  rw [hk]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.IdealPullbackComparison
