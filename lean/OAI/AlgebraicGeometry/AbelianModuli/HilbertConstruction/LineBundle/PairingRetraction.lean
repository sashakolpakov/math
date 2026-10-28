import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorNaturality

/-! # Pairing Retraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PairingRetraction

noncomputable section

/-! Tensor cancellation by a line bundle converts a retraction of an inverse pairing into an actual retraction of module sheaves. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem lineBundlePairing_exists_retraction {X : Scheme.{u}} (K : Line.Bundles.LineBundle X)
    {M P Q : X.Modules} (i : M ⟶ P) (e : Tensor.ProductSheaf.tensorModule M K.sheaf ≅ Q)
    (q : Tensor.ProductSheaf.tensorModule P K.sheaf ⟶ Q)
    (h : Tensor.Bifunctor.tensorModuleMap i (𝟙 K.sheaf) ≫ q = e.hom) :
    ∃ r : P ⟶ M, i ≫ r = 𝟙 M := by
  let F := (TensorEquivalence.lineBundleRightTensorEquivalence K).functor
  let a := TensorEquivalence.lineBundleRightTensorEquivalence_objIso K M
  let b := TensorEquivalence.lineBundleRightTensorEquivalence_objIso K P
  let d : F.obj P ⟶ F.obj M := b.hom ≫ q ≫ e.inv ≫ a.inv
  refine ⟨F.preimage d, ?_⟩
  apply F.map_injective
  rw [F.map_comp, F.map_preimage, F.map_id]
  have hn : F.map i ≫ b.hom = a.hom ≫ Tensor.Bifunctor.tensorModuleMap i (𝟙 K.sheaf) :=
    Module.MonoidalTensorNaturality.moduleMonoidalTensorIso_natural_left i K.sheaf
  have hd : F.map i ≫ d = a.hom ≫ (Tensor.Bifunctor.tensorModuleMap i (𝟙 K.sheaf) ≫ q) ≫ e.inv ≫ a.inv := by
    dsimp only [d]
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
  rw [h] at hd
  exact hd.trans (by
    simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id]
    rfl)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PairingRetraction
