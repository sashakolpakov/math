import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.CoverBaseChange

/-! # Cover Factor Change -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.CoverFactorChange.Construction

noncomputable section

/-! Changing the first factor of an actual finite etale product cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S A B T D : Scheme.{u}} (p : A ⟶ S) (q : B ⟶ S)
  (t : T ⟶ pullback p q) (c : D ⟶ A)

def productCoverFactorChangeIso :
    pullback c (t ≫ pullback.fst p q) ≅
      pullback ((t ≫ (pullbackSymmetry p q).hom) ≫ pullback.snd q p) c :=
  pullbackSymmetry c (t ≫ pullback.fst p q) ≪≫
    pullback.congrHom (by simp) rfl

/-- The changed product cover has the literal projections to the new factor and the base. -/
def productCoverFactorChangeMap :
    pullback c (t ≫ pullback.fst p q) ⟶ pullback (c ≫ p) q :=
  (productCoverFactorChangeIso p q t c).hom ≫
    CoverBaseChange.Construction.productCoverBaseChangeMap q p (t ≫ (pullbackSymmetry p q).hom) c ≫
      (pullbackSymmetry q (c ≫ p)).hom

@[reassoc]
theorem productCoverFactorChangeMap_fst :
    productCoverFactorChangeMap p q t c ≫ pullback.fst (c ≫ p) q =
      pullback.fst c (t ≫ pullback.fst p q) := by
  simp [productCoverFactorChangeMap, productCoverFactorChangeIso,
    CoverBaseChange.Construction.productCoverBaseChangeMap_snd]

@[reassoc]
theorem productCoverFactorChangeMap_snd :
    productCoverFactorChangeMap p q t c ≫ pullback.snd (c ≫ p) q =
      pullback.snd c (t ≫ pullback.fst p q) ≫ t ≫ pullback.snd p q := by
  simp [productCoverFactorChangeMap, productCoverFactorChangeIso,
    CoverBaseChange.Construction.productCoverBaseChangeMap_fst]

theorem productCoverFactorChangeMap_finite [IsFinite t] :
    IsFinite (productCoverFactorChangeMap p q t c) := by
  have := CoverBaseChange.Construction.productCoverBaseChangeMap_finite q p (t ≫ (pullbackSymmetry p q).hom) c
  unfold productCoverFactorChangeMap
  infer_instance

theorem productCoverFactorChangeMap_etale [Etale t] :
    Etale (productCoverFactorChangeMap p q t c) := by
  have := CoverBaseChange.Construction.productCoverBaseChangeMap_etale q p (t ≫ (pullbackSymmetry p q).hom) c
  unfold productCoverFactorChangeMap
  infer_instance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.CoverFactorChange.Construction
