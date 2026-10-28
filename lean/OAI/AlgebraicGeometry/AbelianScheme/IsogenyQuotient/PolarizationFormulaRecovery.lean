import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianFiberComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianMixedProduct
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PicardSquareComparison

/-! # Polarization Formula Recovery -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationFormulaRecovery.Construction

noncomputable section

/-! A recovered Poincare line and a commuting polarization map recover
the actual polarization biextension class on the original product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PicardSquareComparison

variable {S Y : Scheme.{0}} {g h : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Y) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S) (E : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (u : Y ⟶ S)
    (eA : A.scheme ≅ (B.pullback u).scheme)
    (eD : D.abelian.scheme ≅ (E.abelian.pullback u).scheme)
    (p : A.scheme ⟶ D.abelian.scheme) (w : B.scheme ⟶ E.abelian.scheme)
    (hc : eA.hom ≫ (Over.pullback u).map w = p ≫ eD.hom)

include hc in
set_option backward.isDefEq.respectTransparency false in
theorem recovered_polarization_product_square :
    AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.tensorMap u A.scheme B.scheme eA ≫ (w ⊗ₘ 𝟙 B.scheme).left =
      (p ⊗ₘ 𝟙 A.scheme).left ≫ AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u eD eA := by
  let qA := AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u A.scheme B.scheme eA
  let qD := AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u D.abelian.scheme E.abelian.scheme eD
  let q := AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.tensorMap u A.scheme B.scheme eA
  let m := AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u eD eA
  have hp : qA ≫ w.left = p.left ≫ qD :=
    AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap_morphism_comparison u A B eA eD p w hc
  have hwf : (w ⊗ₘ 𝟙 B.scheme).left ≫ (fst E.abelian.scheme B.scheme).left =
      (fst B.scheme B.scheme).left ≫ w.left := Over.tensorHom_left_fst _ _ _ _
  have hws : (w ⊗ₘ 𝟙 B.scheme).left ≫ (snd E.abelian.scheme B.scheme).left =
      (snd B.scheme B.scheme).left := (Over.tensorHom_left_snd _ _ _ _).trans (Category.comp_id _)
  have hpf : (p ⊗ₘ 𝟙 A.scheme).left ≫ (fst D.abelian.scheme A.scheme).left =
      (fst A.scheme A.scheme).left ≫ p.left := Over.tensorHom_left_fst _ _ _ _
  have hps : (p ⊗ₘ 𝟙 A.scheme).left ≫ (snd D.abelian.scheme A.scheme).left =
      (snd A.scheme A.scheme).left := (Over.tensorHom_left_snd _ _ _ _).trans (Category.comp_id _)
  apply Over.tensorObj_ext
  · change (q ≫ (w ⊗ₘ 𝟙 B.scheme).left) ≫ (fst E.abelian.scheme B.scheme).left =
      ((p ⊗ₘ 𝟙 A.scheme).left ≫ m) ≫ (fst E.abelian.scheme B.scheme).left
    rw [Category.assoc, hwf, ← Category.assoc, AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.tensorMap_fst,
      Category.assoc, hp, ← Category.assoc, ← hpf, Category.assoc,
      Category.assoc, AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap_fst]
  · change (q ≫ (w ⊗ₘ 𝟙 B.scheme).left) ≫ (snd E.abelian.scheme B.scheme).left =
      ((p ⊗ₘ 𝟙 A.scheme).left ≫ m) ≫ (snd E.abelian.scheme B.scheme).left
    rw [Category.assoc, hws, AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.tensorMap_snd, Category.assoc,
      AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap_snd, ← Category.assoc, hps]

include hc in
theorem recovered_polarization_biextension_class
    (hP : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u eD eA)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf E.poincare) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.tensorMap u A.scheme B.scheme eA)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (E.poincare.pullback (w ⊗ₘ 𝟙 B.scheme).left)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.poincare.pullback (p ⊗ₘ 𝟙 A.scheme).left) :=
  (AbelianModuli.ReferenceFamily.PicardSquareComparison.picardPullback_square _ _ _ _
    (recovered_polarization_product_square A D B E u eA eD p w hc)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf E.poincare)).trans
      (congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (p ⊗ₘ 𝟙 A.scheme).left) hP)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationFormulaRecovery.Construction
