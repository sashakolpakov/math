import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-! # Family Intrinsic Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.FamilyIntrinsicDescent

noncomputable section

/-! Comparisons on whole product families give native descent data on
product charts. Pulling along the graph of a test point supplies the
comparison on that point; its naturality follows from pseudofunctor
associativity and the naturality of the original family comparisons. -/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v' t
open OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

structure ProductFamilyComparisons {K : Type u} [Category.{v} K]
    [CartesianMonoidalCategory K]
    (F : Pseudofunctor (LocallyDiscrete Kᵒᵖ) Cat.{v', u'})
    (A : K) {B : K} {ι : Type t} {V : ι → K} (j : ∀ i, V i ⟶ B) where
  obj (i : ι) : F.obj (.mk (op (V i ⊗ A)))
  hom {T : K} {i k : ι} (a : T ⟶ V i) (b : T ⟶ V k)
    (h : a ≫ j i = b ≫ j k) :
    (F.map (a ▷ A).op.toLoc).toFunctor.obj (obj i) ⟶
      (F.map (b ▷ A).op.toLoc).toFunctor.obj (obj k)
  hom_self {T : K} {i : ι} (a : T ⟶ V i) : hom a a rfl = 𝟙 _
  hom_comp {T : K} {i k l : ι} (a : T ⟶ V i) (b : T ⟶ V k) (c : T ⟶ V l)
    (hab : a ≫ j i = b ≫ j k) (hbc : b ≫ j k = c ≫ j l) :
    hom a b hab ≫ hom b c hbc = hom a c (hab.trans hbc)
  pullHom_hom {T U : K} {i k : ι} (t : U ⟶ T)
    (a : T ⟶ V i) (b : T ⟶ V k) (h : a ≫ j i = b ≫ j k)
    (a' : U ⟶ V i) (b' : U ⟶ V k) (ha : t ≫ a = a') (hb : t ≫ b = b')
    (h' : a' ≫ j i = b' ≫ j k) :
    pullHom (hom a b h) (t ▷ A) (a' ▷ A) (b' ▷ A)
      ((comp_whiskerRight t a A).symm.trans (congrArg (fun f => f ▷ A) ha))
      ((comp_whiskerRight t b A).symm.trans (congrArg (fun f => f ▷ A) hb)) = hom a' b' h'

namespace ProductFamilyComparisons
variable {K : Type u} [Category.{v} K] [CartesianMonoidalCategory K]
  {F : Pseudofunctor (LocallyDiscrete Kᵒᵖ) Cat.{v', u'}}
  {A B : K} {ι : Type t} {V : ι → K} {j : ∀ i, V i ⟶ B}
  (D : ProductFamilyComparisons F A j)

private def graph {T : K} (q : T ⟶ B ⊗ A) : T ⟶ T ⊗ A :=
  lift (𝟙 T) (q ≫ snd B A)

private theorem parameter_fac {T : K} (q : T ⟶ B ⊗ A) {i : ι}
    (x : T ⟶ V i ⊗ A) (hx : x ≫ (j i ▷ A) = q) :
    (x ≫ fst (V i) A) ≫ j i = q ≫ fst B A := by
  simpa only [Category.assoc, whiskerRight_fst] using
    congrArg (fun f => f ≫ fst B A) hx

private theorem parameter_eq {T : K} (q : T ⟶ B ⊗ A) {i k : ι}
    (x : T ⟶ V i ⊗ A) (y : T ⟶ V k ⊗ A)
    (hx : x ≫ (j i ▷ A) = q) (hy : y ≫ (j k ▷ A) = q) :
    (x ≫ fst (V i) A) ≫ j i = (y ≫ fst (V k) A) ≫ j k :=
  (parameter_fac q x hx).trans (parameter_fac q y hy).symm

private theorem graph_fac {T : K} (q : T ⟶ B ⊗ A) {i : ι}
    (x : T ⟶ V i ⊗ A) (hx : x ≫ (j i ▷ A) = q) :
    graph q ≫ ((x ≫ fst (V i) A) ▷ A) = x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graph, Category.assoc, whiskerRight_fst, lift_fst_assoc, Category.id_comp]
  · simpa only [graph, Category.assoc, whiskerRight_snd, lift_snd] using
      (congrArg (fun f => f ≫ snd B A) hx).symm

private theorem graph_natural {T U : K} (t : U ⟶ T)
    (q : T ⟶ B ⊗ A) (q' : U ⟶ B ⊗ A) (hq : t ≫ q = q') :
    graph q' ≫ (t ▷ A) = t ≫ graph q := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graph, Category.assoc, whiskerRight_fst, lift_fst_assoc,
      lift_fst, Category.id_comp, Category.comp_id]
  · simpa only [graph, Category.assoc, whiskerRight_snd, lift_snd] using
      (congrArg (fun f => f ≫ snd B A) hq).symm

/-- Restrict the whole-family comparison along the graph of an
arbitrary point of the product. -/
def descentHom {T : K} (q : T ⟶ B ⊗ A) {i k : ι}
    (x : T ⟶ V i ⊗ A) (y : T ⟶ V k ⊗ A)
    (hx : x ≫ (j i ▷ A) = q) (hy : y ≫ (j k ▷ A) = q) :
    (F.map x.op.toLoc).toFunctor.obj (D.obj i) ⟶
      (F.map y.op.toLoc).toFunctor.obj (D.obj k) :=
  pullHom (D.hom (x ≫ fst (V i) A) (y ≫ fst (V k) A) (parameter_eq q x y hx hy))
    (graph q) x y (graph_fac q x hx) (graph_fac q y hy)

theorem descentHom_self {T : K} (q : T ⟶ B ⊗ A) {i : ι}
    (x : T ⟶ V i ⊗ A) (hx : x ≫ (j i ▷ A) = q) :
    D.descentHom q x x hx hx = 𝟙 _ := by
  unfold ProductFamilyComparisons.descentHom
  rw [D.hom_self]
  exact Picard.PoincareBundle.PullHom.pullHom_identity _ _ _

theorem descentHom_comp {T : K} (q : T ⟶ B ⊗ A) {i k l : ι}
    (x : T ⟶ V i ⊗ A) (y : T ⟶ V k ⊗ A) (z : T ⟶ V l ⊗ A)
    (hx : x ≫ (j i ▷ A) = q) (hy : y ≫ (j k ▷ A) = q) (hz : z ≫ (j l ▷ A) = q) :
    D.descentHom q x y hx hy ≫ D.descentHom q y z hy hz = D.descentHom q x z hx hz := by
  unfold ProductFamilyComparisons.descentHom
  rw [← Picard.PoincareBundle.PullHom.pullHom_comp, D.hom_comp]

theorem descentHom_pullback {T U : K} (t : U ⟶ T)
    (q : T ⟶ B ⊗ A) (q' : U ⟶ B ⊗ A) (hq : t ≫ q = q') {i k : ι}
    (x : T ⟶ V i ⊗ A) (y : T ⟶ V k ⊗ A)
    (hx : x ≫ (j i ▷ A) = q) (hy : y ≫ (j k ▷ A) = q)
    (x' : U ⟶ V i ⊗ A) (y' : U ⟶ V k ⊗ A)
    (htx : t ≫ x = x') (hty : t ≫ y = y') :
    pullHom (D.descentHom q x y hx hy) t x' y' htx hty =
      D.descentHom q' x' y'
        (by rw [← htx, Category.assoc, hx, hq])
        (by rw [← hty, Category.assoc, hy, hq]) := by
  have hx' : x' ≫ (j i ▷ A) = q' := by rw [← htx, Category.assoc, hx, hq]
  have hy' : y' ≫ (j k ▷ A) = q' := by rw [← hty, Category.assoc, hy, hq]
  let a := x ≫ fst (V i) A
  let b := y ≫ fst (V k) A
  let a' := x' ≫ fst (V i) A
  let b' := y' ≫ fst (V k) A
  have ha : t ≫ a = a' := by dsimp [a, a']; rw [← Category.assoc, htx]
  have hb : t ≫ b = b' := by dsimp [b, b']; rw [← Category.assoc, hty]
  have h : a ≫ j i = b ≫ j k := parameter_eq q x y hx hy
  have h' : a' ≫ j i = b' ≫ j k := parameter_eq q' x' y' hx' hy'
  have hta : (t ▷ A) ≫ (a ▷ A) = a' ▷ A :=
    (comp_whiskerRight t a A).symm.trans (congrArg (fun f => f ▷ A) ha)
  have htb : (t ▷ A) ≫ (b ▷ A) = b' ▷ A :=
    (comp_whiskerRight t b A).symm.trans (congrArg (fun f => f ▷ A) hb)
  have hγa : graph q ≫ (a ▷ A) = x := graph_fac q x hx
  have hγb : graph q ≫ (b ▷ A) = y := graph_fac q y hy
  have hγa' : graph q' ≫ (a' ▷ A) = x' := graph_fac q' x' hx'
  have hγb' : graph q' ≫ (b' ▷ A) = y' := graph_fac q' y' hy'
  have hga : (t ≫ graph q) ≫ (a ▷ A) = x' := by rw [Category.assoc, hγa, htx]
  have hgb : (t ≫ graph q) ≫ (b ▷ A) = y' := by rw [Category.assoc, hγb, hty]
  have hga' : (graph q' ≫ (t ▷ A)) ≫ (a ▷ A) = x' := by rw [Category.assoc, hta, hγa']
  have hgb' : (graph q' ≫ (t ▷ A)) ≫ (b ▷ A) = y' := by rw [Category.assoc, htb, hγb']
  change pullHom (pullHom (D.hom a b h) (graph q) x y hγa hγb) t x' y' htx hty =
    pullHom (D.hom a' b' h') (graph q') x' y' hγa' hγb'
  rw [pullHom_pullHom]
  calc
    pullHom (D.hom a b h) (t ≫ graph q) x' y' hga hgb =
        pullHom (D.hom a b h) (graph q' ≫ (t ▷ A)) x' y' hga' hgb' :=
      Picard.PoincareBundle.PullHom.pullHom_congr _ _ _ (graph_natural t q q' hq).symm x' y' hga hgb hga' hgb'
    _ = pullHom (pullHom (D.hom a b h) (t ▷ A) (a' ▷ A) (b' ▷ A) hta htb)
        (graph q') x' y' hγa' hγb' :=
      (pullHom_pullHom (D.hom a b h) (t ▷ A) (a' ▷ A) (b' ▷ A)
        (graph q') x' y' hta htb hγa' hγb').symm
    _ = pullHom (D.hom a' b' h') (graph q') x' y' hγa' hγb' := by
      rw [D.pullHom_hom t a b h a' b' ha hb h']

/-- Genuine native descent data on the product-chart cover. -/
def descentData : F.DescentData (fun i => j i ▷ A) where
  obj := D.obj
  hom := fun {_} q {_ _} x y hx hy => D.descentHom q x y hx hy
  hom_self := fun {_} q {_} x hx => D.descentHom_self q x hx
  hom_comp := fun {_} q {_ _ _} x y z hx hy hz => D.descentHom_comp q x y z hx hy hz
  pullHom_hom := fun {_ _} t q q' hq {_ _} x y hx hy x' y' htx hty =>
    D.descentHom_pullback t q q' hq x y hx hy x' y' htx hty

end ProductFamilyComparisons

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.FamilyIntrinsicDescent
