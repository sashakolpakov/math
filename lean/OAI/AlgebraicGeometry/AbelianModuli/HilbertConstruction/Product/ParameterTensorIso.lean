import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterIsoCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ProductProjection

/-! # Parameter Tensor Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterTensorIso

noncomputable section

/-! The geometric comparison of a product is the product of the individual comparisons, followed by the categorical product comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} {T M : Over S} (f : T ⟶ M) (A B : Over S)

theorem productParameterBaseChangeIso_snd :
    (ParameterBaseChange.productParameterBaseChangeIso f A B).hom ≫
      (Over.pullback f.left).map (snd ((Over.pullback M.hom).obj A) ((Over.pullback M.hom).obj B)) =
        snd ((Over.pullback T.hom).obj A) ((Over.pullback T.hom).obj B) ≫ (Single.ParameterBaseChange.singleParameterBaseChangeIso f B).hom :=
  Cartesian.OverIsoNaturality.cartesianAmbientOverIso_natural f.left (ParameterBaseChange.productParameterBaseChangeMap f A B) (Single.ParameterBaseChange.singleParameterBaseChangeMap f B)
    (ParameterBaseChange.productParameterBaseChangeMap_isPullback f A B) (Single.ParameterBaseChange.singleParameterBaseChangeMap_isPullback f B)
    (snd _ _) (snd _ _) (ParameterProjections.productParameterBaseChangeMap_snd f A B)

theorem productParameterBaseChangeIso_tensor :
    ((Single.ParameterBaseChange.singleParameterBaseChangeIso f A).hom ⊗ₘ (Single.ParameterBaseChange.singleParameterBaseChangeIso f B).hom) ≫
      (Functor.Monoidal.μIso (Over.pullback f.left) ((Over.pullback M.hom).obj A) ((Over.pullback M.hom).obj B)).hom =
        (ParameterBaseChange.productParameterBaseChangeIso f A B).hom := by
  apply (cancel_mono (Functor.Monoidal.μIso (Over.pullback f.left)
    ((Over.pullback M.hom).obj A) ((Over.pullback M.hom).obj B)).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext
  · rw [tensorHom_fst, Category.assoc, Pullback.ProductProjection.overPullbackProductIso_inv_fst]
    exact (ParameterIsoCompatibility.productParameterBaseChangeIso_fst f A B).symm
  · rw [tensorHom_snd, Category.assoc, Pullback.ProductProjection.overPullbackProductIso_inv_snd]
    exact (productParameterBaseChangeIso_snd f A B).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterTensorIso
