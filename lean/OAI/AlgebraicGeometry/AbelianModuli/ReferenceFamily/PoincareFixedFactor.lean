import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareFixedComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianMixedProduct

/-! # Poincare Fixed Factor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareFixedFactor

noncomputable section

/-! The fixed-family parameter cover and the original simultaneous
product cover give exactly the same map to the descended product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem fixedFamilyPoincareComparison_factor {S T : Scheme.{0}} {g : ℕ}
    {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g T} (D : HilbertConstruction.Dual.Data.DualAbelianData A) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (u : T ⟶ S)
    (eA : A.scheme ≅ (B.pullback u).scheme) (E : Over S)
    (eD : D.abelian.scheme ≅ (Over.pullback u).obj E)
    (q : (Over.map u).obj D.abelian.scheme ⟶ E)
    (hq : q.left = CartesianFiberComparison.CartesianFamily.totalMap u D.abelian.scheme E eD) :
    (PoincareFixedComparison.fixedFamilyPoincareComparison D B u eA).hom ≫ (q ▷ B.scheme).left =
      CartesianMixedProduct.CartesianFamily.mixedMap u eD eA := by
  let V := (Over.map u).obj D.abelian.scheme
  let c := (PoincareFixedComparison.fixedFamilyPoincareComparison D B u eA).hom
  let p := (q ▷ B.scheme).left
  let m := CartesianMixedProduct.CartesianFamily.mixedMap u eD eA
  have hp : p ≫ (fst E B.scheme).left = (fst V B.scheme).left ≫ q.left :=
    congrArg Over.Hom.left (whiskerRight_fst q B.scheme)
  have hs : p ≫ (snd E B.scheme).left = (snd V B.scheme).left :=
    congrArg Over.Hom.left (whiskerRight_snd q B.scheme)
  have hc : c ≫ (fst V B.scheme).left = (fst D.abelian.scheme A.scheme).left :=
    PoincareFixedComparison.fixedFamilyPoincareComparison_fst D B u eA
  have hd : c ≫ (snd V B.scheme).left =
      (snd D.abelian.scheme A.scheme).left ≫ CartesianFiberComparison.CartesianFamily.totalMap u A.scheme B.scheme eA :=
    PoincareFixedComparison.fixedFamilyPoincareComparison_snd D B u eA
  have hm : m ≫ (fst E B.scheme).left = (fst D.abelian.scheme A.scheme).left ≫
      CartesianFiberComparison.CartesianFamily.totalMap u D.abelian.scheme E eD := CartesianMixedProduct.CartesianFamily.mixedMap_fst u eD eA
  have hn : m ≫ (snd E B.scheme).left = (snd D.abelian.scheme A.scheme).left ≫
      CartesianFiberComparison.CartesianFamily.totalMap u A.scheme B.scheme eA := CartesianMixedProduct.CartesianFamily.mixedMap_snd u eD eA
  apply Over.tensorObj_ext
  · change (c ≫ p) ≫ (fst E B.scheme).left = m ≫ (fst E B.scheme).left
    rw [Category.assoc, hp, ← Category.assoc, hc, hq, hm]
  · change (c ≫ p) ≫ (snd E B.scheme).left = m ≫ (snd E B.scheme).left
    rw [Category.assoc, hs, hd, hn]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareFixedFactor
