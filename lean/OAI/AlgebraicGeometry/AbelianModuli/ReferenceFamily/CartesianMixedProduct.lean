import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianFiberComparison

/-! # Cartesian Mixed Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily

noncomputable section

/-! The product of two independently descended families has its
actual mixed cartesian comparison and both exact total projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S T : Scheme.{0}} (u : T ⟶ S) {A D : Over T} {B E : Over S}
    (eA : A ≅ (Over.pullback u).obj B) (eD : D ≅ (Over.pullback u).obj E)

def mixedComparison : A ⊗ D ≅ (Over.pullback u).obj (B ⊗ E) :=
  tensorIso eA eD ≪≫ Functor.Monoidal.μIso (Over.pullback u) B E

def mixedMap : (A ⊗ D).left ⟶ (B ⊗ E).left :=
  CartesianFiberComparison.CartesianFamily.totalMap u (A ⊗ D) (B ⊗ E) (mixedComparison u eA eD)

theorem mixedMap_isPullback : IsPullback (A ⊗ D).hom (mixedMap u eA eD) u (B ⊗ E).hom :=
  CartesianFiberComparison.CartesianFamily.totalMap_isPullback _ _ _ _

theorem mixedMap_fst : mixedMap u eA eD ≫ (fst B E).left =
    (fst A D).left ≫ CartesianFiberComparison.CartesianFamily.totalMap u A B eA := by
  let m := (eA.hom ⊗ₘ eD.hom).left
  let k := (Functor.Monoidal.μIso (Over.pullback u) B E).hom.left
  let p := pullback.fst (B ⊗ E).hom u
  have hk : k ≫ p ≫ (fst B E).left =
      (fst ((Over.pullback u).obj B) ((Over.pullback u).obj E)).left ≫ pullback.fst B.hom u :=
    Over.μ_pullback_left_fst_fst B E
  have hm : m ≫ (fst ((Over.pullback u).obj B) ((Over.pullback u).obj E)).left =
      (fst A D).left ≫ eA.hom.left := Over.tensorHom_left_fst _ _ _ _
  change ((m ≫ k) ≫ p) ≫ (fst B E).left = _
  rw [Category.assoc, Category.assoc, hk, ← Category.assoc, hm, Category.assoc]
  rfl

theorem mixedMap_snd : mixedMap u eA eD ≫ (snd B E).left =
    (snd A D).left ≫ CartesianFiberComparison.CartesianFamily.totalMap u D E eD := by
  let m := (eA.hom ⊗ₘ eD.hom).left
  let k := (Functor.Monoidal.μIso (Over.pullback u) B E).hom.left
  let p := pullback.fst (B ⊗ E).hom u
  have hk : k ≫ p ≫ (snd B E).left =
      (snd ((Over.pullback u).obj B) ((Over.pullback u).obj E)).left ≫ pullback.fst E.hom u :=
    Over.μ_pullback_left_fst_snd B E
  have hm : m ≫ (snd ((Over.pullback u).obj B) ((Over.pullback u).obj E)).left =
      (snd A D).left ≫ eD.hom.left := Over.tensorHom_left_snd _ _ _ _
  change ((m ≫ k) ≫ p) ≫ (snd B E).left = _
  rw [Category.assoc, Category.assoc, hk, ← Category.assoc, hm, Category.assoc]
  rfl

theorem mixedMap_invariant
    (a : A.left ⟶ A.left) (d : D.left ⟶ D.left) (c : (A ⊗ D).left ⟶ (A ⊗ D).left)
    (hf : c ≫ (fst A D).left = (fst A D).left ≫ a)
    (hs : c ≫ (snd A D).left = (snd A D).left ≫ d)
    (ha : a ≫ CartesianFiberComparison.CartesianFamily.totalMap u A B eA = CartesianFiberComparison.CartesianFamily.totalMap u A B eA)
    (hd : d ≫ CartesianFiberComparison.CartesianFamily.totalMap u D E eD = CartesianFiberComparison.CartesianFamily.totalMap u D E eD) :
    c ≫ mixedMap u eA eD = mixedMap u eA eD := by
  apply Over.tensorObj_ext
  · change (c ≫ mixedMap u eA eD) ≫ (fst B E).left = mixedMap u eA eD ≫ (fst B E).left
    rw [Category.assoc, mixedMap_fst, ← Category.assoc, hf, Category.assoc, ha]
  · change (c ≫ mixedMap u eA eD) ≫ (snd B E).left = mixedMap u eA eD ≫ (snd B E).left
    rw [Category.assoc, mixedMap_snd, ← Category.assoc, hs, Category.assoc, hd]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily
