import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition

/-! # Pull Iso Laws -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PullIsoLaws.Construction

noncomputable section

/-! Unit and composition laws for the native pullback of fiber isomorphisms. -/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

open OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

variable {C : Type u} [Category.{v} C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
variable {A B D T U : C}
variable {L : F.obj (.mk (op A))} {M : F.obj (.mk (op B))} {N : F.obj (.mk (op D))}
variable {x : T ⟶ A} {y : T ⟶ B} {z : T ⟶ D}

theorem pullIso_refl (t : U ⟶ T) (x' : U ⟶ A) (hx : t ≫ x = x') :
    Picard.PoincareBundle.PullbackFiberComposition.pullIso F (Iso.refl ((F.map x.op.toLoc).toFunctor.obj L)) t x' x' hx hx = Iso.refl _ := by
  apply Iso.ext
  exact Picard.PoincareBundle.PullHom.pullHom_identity t x' hx

theorem pullIso_trans
    (e : (F.map x.op.toLoc).toFunctor.obj L ≅ (F.map y.op.toLoc).toFunctor.obj M)
    (e' : (F.map y.op.toLoc).toFunctor.obj M ≅ (F.map z.op.toLoc).toFunctor.obj N)
    (t : U ⟶ T) (x' : U ⟶ A) (y' : U ⟶ B) (z' : U ⟶ D)
    (hx : t ≫ x = x') (hy : t ≫ y = y') (hz : t ≫ z = z') :
    Picard.PoincareBundle.PullbackFiberComposition.pullIso F e t x' y' hx hy ≪≫ Picard.PoincareBundle.PullbackFiberComposition.pullIso F e' t y' z' hy hz =
      Picard.PoincareBundle.PullbackFiberComposition.pullIso F (e ≪≫ e') t x' z' hx hz := by
  apply Iso.ext
  exact (Picard.PoincareBundle.PullHom.pullHom_comp e.hom e'.hom t x' y' z' hx hy hz).symm

theorem pullIso_congr
    (e : (F.map x.op.toLoc).toFunctor.obj L ≅ (F.map y.op.toLoc).toFunctor.obj M)
    (t t' : U ⟶ T) (ht : t = t') (x' : U ⟶ A) (y' : U ⟶ B)
    (hx : t ≫ x = x') (hy : t ≫ y = y') (hx' : t' ≫ x = x') (hy' : t' ≫ y = y') :
    Picard.PoincareBundle.PullbackFiberComposition.pullIso F e t x' y' hx hy = Picard.PoincareBundle.PullbackFiberComposition.pullIso F e t' x' y' hx' hy' := by
  subst t'
  rfl

theorem pullIso_trans_of_base_eq
    (e : (F.map x.op.toLoc).toFunctor.obj L ≅ (F.map y.op.toLoc).toFunctor.obj M)
    (e' : (F.map y.op.toLoc).toFunctor.obj M ≅ (F.map z.op.toLoc).toFunctor.obj N)
    (t t' : U ⟶ T) (ht : t' = t) (x' : U ⟶ A) (y' : U ⟶ B) (z' : U ⟶ D)
    (hx : t ≫ x = x') (hy : t ≫ y = y') (hz : t ≫ z = z')
    (hy' : t' ≫ y = y') (hz' : t' ≫ z = z') :
    Picard.PoincareBundle.PullbackFiberComposition.pullIso F e t x' y' hx hy ≪≫ Picard.PoincareBundle.PullbackFiberComposition.pullIso F e' t' y' z' hy' hz' =
      Picard.PoincareBundle.PullbackFiberComposition.pullIso F (e ≪≫ e') t x' z' hx hz :=
  (congrArg (fun a => Picard.PoincareBundle.PullbackFiberComposition.pullIso F e t x' y' hx hy ≪≫ a)
    (pullIso_congr F e' t' t ht y' z' hy' hz' hy hz)).trans
      (pullIso_trans F e e' t x' y' z' hx hy hz)

theorem pullIso_square_of_eq {V W : C}
    (e : (F.map x.op.toLoc).toFunctor.obj L ≅ (F.map y.op.toLoc).toFunctor.obj M)
    (a : V ⟶ T) (xV : V ⟶ A) (yV : V ⟶ B)
    (b : W ⟶ T) (xW : W ⟶ A) (yW : W ⟶ B)
    (t : U ⟶ V) (s : U ⟶ W) (xU : U ⟶ A) (yU : U ⟶ B)
    (haX : a ≫ x = xV) (haY : a ≫ y = yV)
    (hbX : b ≫ x = xW) (hbY : b ≫ y = yW)
    (htX : t ≫ xV = xU) (htY : t ≫ yV = yU)
    (hsX : s ≫ xW = xU) (hsY : s ≫ yW = yU) (h : t ≫ a = s ≫ b)
    (e' : (F.map xW.op.toLoc).toFunctor.obj L ≅ (F.map yW.op.toLoc).toFunctor.obj M)
    (he : Picard.PoincareBundle.PullbackFiberComposition.pullIso F e b xW yW hbX hbY = e') :
    Picard.PoincareBundle.PullbackFiberComposition.pullIso F (Picard.PoincareBundle.PullbackFiberComposition.pullIso F e a xV yV haX haY) t xU yU htX htY =
      Picard.PoincareBundle.PullbackFiberComposition.pullIso F e' s xU yU hsX hsY := by
  subst e'
  apply Iso.ext
  have h₁ := pullHom_pullHom e.hom a xV yV t xU yU haX haY htX htY
  have h₂ := pullHom_pullHom e.hom b xW yW s xU yU hbX hbY hsX hsY
  exact h₁.trans ((Picard.PoincareBundle.PullHom.pullHom_congr e.hom (t ≫ a) (s ≫ b) h xU yU
    (by rw [Category.assoc, haX, htX]) (by rw [Category.assoc, haY, htY])
    (by rw [Category.assoc, hbX, hsX]) (by rw [Category.assoc, hbY, hsY])).trans h₂.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PullIsoLaws.Construction
