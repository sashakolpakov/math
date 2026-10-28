import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.TensorSelfSymmetry

/-! # Triple Tensor Factor Swap -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TripleTensorFactorSwap

noncomputable section

/-! Swapping the two inducing-line factors in a three-factor line formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {X : Scheme.{u}}

theorem tensorCongr_refl (M N : X.Modules) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Iso.refl M) (Iso.refl N) = Iso.refl (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) := by
  let : MonoidalCategory X.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory
  apply Iso.ext
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((𝟙 M.val) ⊗ₘ (𝟙 N.val)) = 𝟙 (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)
  rw [id_tensorHom_id]
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_id _

/-- Keep the first factor and exchange the second and third actual tensor factors. -/
def swap (M N P : X.Modules) : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P ≅ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M P) N :=
  Homomorphisms.TensorAssociativity.Construction.tensorModuleAssocIso M N P ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Iso.refl M) (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso N P) ≪≫
    (Homomorphisms.TensorAssociativity.Construction.tensorModuleAssocIso M P N).symm

/-- On the diagonal the inducing-line swap is exactly the identity, in every characteristic. -/
theorem swap_self (M N : X.Modules) (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N) :
    swap M N N = Iso.refl (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) N) := by
  rw [swap, Line.TensorSelfSymmetry.commIso_self hN, tensorCongr_refl, Iso.refl_trans,
    Iso.self_symm_id]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TripleTensorFactorSwap
