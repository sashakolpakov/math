import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-! # Pull Hom -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

noncomputable section

/-!
# Elementary compatibility of pullback morphisms for PoincareBundle equivariant descent
-/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {A B D T T' : C} {L : F.obj (.mk (op A))} {M : F.obj (.mk (op B))}
  {N : F.obj (.mk (op D))}
  {x : T ⟶ A} {y : T ⟶ B} {z : T ⟶ D}

/-- Equal base morphisms give the same pullback morphism, independently of compatibility proofs. -/
theorem pullHom_congr
    (φ : (F.map x.op.toLoc).toFunctor.obj L ⟶ (F.map y.op.toLoc).toFunctor.obj M)
    (g g' : T' ⟶ T) (h : g = g') (x' : T' ⟶ A) (y' : T' ⟶ B)
    (hx : g ≫ x = x') (hy : g ≫ y = y')
    (hx' : g' ≫ x = x') (hy' : g' ≫ y = y') :
    pullHom φ g x' y' hx hy = pullHom φ g' x' y' hx' hy' := by
  subst g'
  rfl

/-- Pullback preserves composition when all target maps are specified. -/
theorem pullHom_comp
    (φ : (F.map x.op.toLoc).toFunctor.obj L ⟶ (F.map y.op.toLoc).toFunctor.obj M)
    (ψ : (F.map y.op.toLoc).toFunctor.obj M ⟶ (F.map z.op.toLoc).toFunctor.obj N)
    (g : T' ⟶ T) (x' : T' ⟶ A) (y' : T' ⟶ B) (z' : T' ⟶ D)
    (hx : g ≫ x = x') (hy : g ≫ y = y') (hz : g ≫ z = z') :
    pullHom (φ ≫ ψ) g x' z' hx hz =
      pullHom φ g x' y' hx hy ≫ pullHom ψ g y' z' hy hz := by
  let ex := (Cat.Hom.toNatIso
    (F.mapComp' x.op.toLoc g.op.toLoc x'.op.toLoc (by aesop))).app L
  let ey := (Cat.Hom.toNatIso
    (F.mapComp' y.op.toLoc g.op.toLoc y'.op.toLoc (by aesop))).app M
  let ez := (Cat.Hom.toNatIso
    (F.mapComp' z.op.toLoc g.op.toLoc z'.op.toLoc (by aesop))).app N
  let G := (F.map g.op.toLoc).toFunctor
  change ex.hom ≫ G.map (φ ≫ ψ) ≫ ez.inv =
    (ex.hom ≫ G.map φ ≫ ey.inv) ≫ (ey.hom ≫ G.map ψ ≫ ez.inv)
  rw [G.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Pullback of an identity morphism is an identity morphism. -/
theorem pullHom_identity (g : T' ⟶ T) (x' : T' ⟶ A) (hx : g ≫ x = x') :
    pullHom (𝟙 ((F.map x.op.toLoc).toFunctor.obj L)) g x' x' hx hx = 𝟙 _ := by
  let ex := (Cat.Hom.toNatIso
    (F.mapComp' x.op.toLoc g.op.toLoc x'.op.toLoc (by aesop))).app L
  let G := (F.map g.op.toLoc).toFunctor
  change ex.hom ≫ G.map (𝟙 _) ≫ ex.inv = 𝟙 _
  erw [G.map_id, Category.id_comp, ex.hom_inv_id]

/-- Replacing the common base map by an equal map does not change a descent morphism. -/
theorem descentHom_base_congr {X Y : C} (f : X ⟶ Y)
    (D : F.DescentData (fun (_ : PUnit.{1}) => f))
    (q q' : T ⟶ Y) (hq : q = q') (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) (hx' : x ≫ f = q') (hy' : y ≫ f = q') :
    D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
      D.hom q' (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx' hy' := by
  subst q'
  rfl

/-- Gluing isomorphisms compose even when each pair is presented with its own base map. -/
theorem descentIso_comp {X Y : C} (f : X ⟶ Y)
    (D : F.DescentData (fun (_ : PUnit.{1}) => f)) (x y z : T ⟶ X)
    (hxy : x ≫ f = y ≫ f) (hyz : y ≫ f = z ≫ f) :
    (D.iso (x ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y rfl hxy.symm).hom ≫
        (D.iso (y ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) y z rfl hyz.symm).hom =
      (D.iso (x ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) x z rfl (hxy.trans hyz).symm).hom := by
  have hb := descentHom_base_congr f D (y ≫ f) (x ≫ f) hxy.symm y z
    rfl hyz.symm hxy.symm (hxy.trans hyz).symm
  exact (congrArg (fun m => D.hom (x ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      x y rfl hxy.symm ≫ m) hb).trans
    (D.hom_comp (x ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (i₃ := PUnit.unit)
      x y z rfl hxy.symm (hxy.trans hyz).symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom
