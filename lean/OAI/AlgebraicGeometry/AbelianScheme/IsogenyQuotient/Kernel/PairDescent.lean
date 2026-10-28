import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.PairCechMaps
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

/-! # Pair Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.PairDescent.Construction.KernelPairDescent

noncomputable section

/-! An isomorphism on the actual kernel pair, with diagonal and
triple-overlap identities, gives ordinary descent data on every test object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

open OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y : C} (f : X ⟶ Y)
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) (L : F.obj (.mk (op X)))

abbrev pointObject {T : C} (x : T ⟶ X) := (F.map x.op.toLoc).toFunctor.obj L

structure Datum where
  gluingIso : pointObject F L (pullback.fst f f) ≅ pointObject F L (pullback.snd f f)
  unit : pullHom gluingIso.hom (PairCechMaps.Construction.KernelPairDescent.diagonal f) (𝟙 X) (𝟙 X) (PairCechMaps.Construction.KernelPairDescent.diagonal_fst f) (PairCechMaps.Construction.KernelPairDescent.diagonal_snd f) = 𝟙 _
  cocycle :
    pullHom gluingIso.hom (PairCechMaps.Construction.KernelPairDescent.first f) (PairCechMaps.Construction.KernelPairDescent.source f) (PairCechMaps.Construction.KernelPairDescent.middle f) rfl rfl ≫
      pullHom gluingIso.hom (PairCechMaps.Construction.KernelPairDescent.second f) (PairCechMaps.Construction.KernelPairDescent.middle f) (PairCechMaps.Construction.KernelPairDescent.target f) (PairCechMaps.Construction.KernelPairDescent.second_middle f) rfl =
    pullHom gluingIso.hom (PairCechMaps.Construction.KernelPairDescent.outer f) (PairCechMaps.Construction.KernelPairDescent.source f) (PairCechMaps.Construction.KernelPairDescent.target f) (PairCechMaps.Construction.KernelPairDescent.outer_source f) (PairCechMaps.Construction.KernelPairDescent.outer_target f)

variable (D : Datum f F L)

def transport {T : C} (x y : T ⟶ X) (h : x ≫ f = y ≫ f) : pointObject F L x ⟶ pointObject F L y :=
  pullHom D.gluingIso.hom (PairCechMaps.Construction.KernelPairDescent.pair f x y h) x y (PairCechMaps.Construction.KernelPairDescent.pair_fst f x y h) (PairCechMaps.Construction.KernelPairDescent.pair_snd f x y h)

theorem transport_self {T : C} (x : T ⟶ X) : transport f F L D x x rfl = 𝟙 _ := by
  have h0 : pullHom (pullHom D.gluingIso.hom (PairCechMaps.Construction.KernelPairDescent.diagonal f) (𝟙 X) (𝟙 X)
      (PairCechMaps.Construction.KernelPairDescent.diagonal_fst f) (PairCechMaps.Construction.KernelPairDescent.diagonal_snd f)) x x x
      (Category.comp_id x) (Category.comp_id x) = 𝟙 _ := by
    rw [D.unit]
    exact Picard.PoincareBundle.PullHom.pullHom_identity x x (Category.comp_id x)
  have h1 := pullHom_pullHom D.gluingIso.hom (PairCechMaps.Construction.KernelPairDescent.diagonal f) (𝟙 X) (𝟙 X) x x x
    (PairCechMaps.Construction.KernelPairDescent.diagonal_fst f) (PairCechMaps.Construction.KernelPairDescent.diagonal_snd f) (Category.comp_id x) (Category.comp_id x)
  have h2 := Picard.PoincareBundle.PullHom.pullHom_congr D.gluingIso.hom (PairCechMaps.Construction.KernelPairDescent.pair f x x rfl) (x ≫ PairCechMaps.Construction.KernelPairDescent.diagonal f)
    (PairCechMaps.Construction.KernelPairDescent.pair_self f x) x x (PairCechMaps.Construction.KernelPairDescent.pair_fst f x x rfl) (PairCechMaps.Construction.KernelPairDescent.pair_snd f x x rfl)
    (by rw [Category.assoc, PairCechMaps.Construction.KernelPairDescent.diagonal_fst, Category.comp_id])
    (by rw [Category.assoc, PairCechMaps.Construction.KernelPairDescent.diagonal_snd, Category.comp_id])
  exact h2.trans (h1.symm.trans h0)

theorem transport_pullback {T U : C} (g : U ⟶ T) (x y : T ⟶ X) (h : x ≫ f = y ≫ f)
    (x' y' : U ⟶ X) (h' : x' ≫ f = y' ≫ f) (hx : g ≫ x = x') (hy : g ≫ y = y') :
    pullHom (transport f F L D x y h) g x' y' hx hy = transport f F L D x' y' h' := by
  have h1 := pullHom_pullHom D.gluingIso.hom (PairCechMaps.Construction.KernelPairDescent.pair f x y h) x y g x' y'
    (PairCechMaps.Construction.KernelPairDescent.pair_fst f x y h) (PairCechMaps.Construction.KernelPairDescent.pair_snd f x y h) hx hy
  have h2 := Picard.PoincareBundle.PullHom.pullHom_congr D.gluingIso.hom (g ≫ PairCechMaps.Construction.KernelPairDescent.pair f x y h) (PairCechMaps.Construction.KernelPairDescent.pair f x' y' h')
    (PairCechMaps.Construction.KernelPairDescent.pair_natural f g x y h x' y' h' hx hy) x' y'
    (by rw [Category.assoc, PairCechMaps.Construction.KernelPairDescent.pair_fst, hx]) (by rw [Category.assoc, PairCechMaps.Construction.KernelPairDescent.pair_snd, hy])
    (PairCechMaps.Construction.KernelPairDescent.pair_fst f x' y' h') (PairCechMaps.Construction.KernelPairDescent.pair_snd f x' y' h')
  exact h1.trans h2

theorem transport_comp {T : C} (x y z : T ⟶ X)
    (hxy : x ≫ f = y ≫ f) (hyz : y ≫ f = z ≫ f) :
    transport f F L D x y hxy ≫ transport f F L D y z hyz =
      transport f F L D x z (hxy.trans hyz) := by
  let t := PairCechMaps.Construction.KernelPairDescent.triple f x y z hxy hyz
  have hs : t ≫ PairCechMaps.Construction.KernelPairDescent.source f = x := by
    rw [PairCechMaps.Construction.KernelPairDescent.source, ← Category.assoc, PairCechMaps.Construction.KernelPairDescent.triple_first, PairCechMaps.Construction.KernelPairDescent.pair_fst]
  have hm : t ≫ PairCechMaps.Construction.KernelPairDescent.middle f = y := by
    rw [PairCechMaps.Construction.KernelPairDescent.middle, ← Category.assoc, PairCechMaps.Construction.KernelPairDescent.triple_first, PairCechMaps.Construction.KernelPairDescent.pair_snd]
  have ht : t ≫ PairCechMaps.Construction.KernelPairDescent.target f = z := by
    rw [PairCechMaps.Construction.KernelPairDescent.target, ← Category.assoc, PairCechMaps.Construction.KernelPairDescent.triple_second, PairCechMaps.Construction.KernelPairDescent.pair_snd]
  have H := congrArg (fun φ : pointObject F L (PairCechMaps.Construction.KernelPairDescent.source f) ⟶ pointObject F L (PairCechMaps.Construction.KernelPairDescent.target f) =>
    pullHom φ t x z hs ht) D.cocycle
  rw [Picard.PoincareBundle.PullHom.pullHom_comp _ _ t x y z hs hm ht] at H
  simpa only [transport, pullHom_pullHom, t, PairCechMaps.Construction.KernelPairDescent.triple_first, PairCechMaps.Construction.KernelPairDescent.triple_second, PairCechMaps.Construction.KernelPairDescent.triple_outer] using H

def toDescentData : F.DescentData (fun (_ : PUnit.{1}) => f) where
  obj _ := L
  hom _T _p _i _j x y hx hy := transport f F L D x y (hx.trans hy.symm)
  hom_self _T _p _i x _hx := transport_self f F L D x
  hom_comp _T _p _i _j _k x y z hx hy hz :=
    transport_comp f F L D x y z (hx.trans hy.symm) (hy.trans hz.symm)
  pullHom_hom _U _T g _p _p' _hp _i _j x y hx hy x' y' htx hty :=
    transport_pullback f F L D g x y (hx.trans hy.symm) x' y' _ htx hty

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.PairDescent.Construction.KernelPairDescent
