import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperFunctionsEq

/-! # Proper Affine -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperAffine.Construction.ProperAffineRigidity

noncomputable section

/-! Actual factorization through a rational point for maps from proper connected reduced schemes to affine schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem hom_eq_of_appTop {X Y : Scheme.{u}} [IsAffine Y] (f g : X ⟶ Y)
    (h : f.appTop = g.appTop) : f = g := by
  apply (cancel_mono Y.toSpecΓ).mp
  rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, h]

theorem factor {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    (e : Spec (.of K) ⟶ X.left) (he : e ≫ X.hom = 𝟙 _)
    {Y : Scheme.{u}} [IsAffine Y] (f : X.left ⟶ Y) : f = X.hom ≫ e ≫ f := by
  have := ProperFunctionsEq.Construction.ProperFunctions.isIso_appTop_of_section X e he
  have hc : X.hom.appTop ≫ e.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
  have hc' : e.appTop ≫ X.hom.appTop = 𝟙 _ := by
    apply (cancel_epi X.hom.appTop).mp
    rw [← Category.assoc, hc, Category.comp_id, Category.id_comp]
  apply hom_eq_of_appTop
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Category.assoc, hc', Category.comp_id]

theorem points_eq {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    {Y : Scheme.{u}} [IsAffine Y] (f : X.left ⟶ Y)
    (a b : Spec (.of K) ⟶ X.left) (ha : a ≫ X.hom = 𝟙 _) (hb : b ≫ X.hom = 𝟙 _) :
    a ≫ f = b ≫ f := by
  conv_lhs => rw [factor X b hb f]
  rw [← Category.assoc, ha, Category.id_comp]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperAffine.Construction.ProperAffineRigidity
