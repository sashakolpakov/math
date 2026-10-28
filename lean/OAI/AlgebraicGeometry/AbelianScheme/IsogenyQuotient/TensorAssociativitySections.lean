import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorSymmetrySections

/-! # Tensor Associativity Sections -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorAssociativitySections.Construction

noncomputable section

/-! Explicit section formulas for the right trilinear universal
property and the actual associator of the sheaf tensor product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M N P Q : X.Modules}

theorem tensorRightTrilinearEquiv_app_tensor (f : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule N P) ⟶ Q)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) :
    (Picard.Homomorphisms.TensorAssociativity.Construction.tensorRightTrilinearEquiv M N P Q f).app U m n p =
      f.app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule N P)).app U m ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear N P).app U n p)) := by
  change (Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv N P M Q
    ((AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule N P)).inv ≫ f ≫ 𝟙 Q)).app U n p m = _
  rw [Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv_apply]
  change f.app U ((AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule N P)).inv.app U
    ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule N P) M).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear N P).app U n p) m)) = _
  rw [TensorSymmetrySections.Construction.tensorModuleCommIso_inv_app_tensor]

theorem tensorModuleAssocIso_trilinear (M N P : X.Modules) :
    Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv M N P (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule N P)) (Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleAssocIso M N P).hom =
      Picard.Homomorphisms.TensorAssociativity.Construction.tensorRightTrilinearEquiv M N P (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule N P)) (𝟙 _) :=
  (Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv M N P _).apply_symm_apply _

theorem tensorModuleAssocIso_app_tensor (M N P : X.Modules)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) :
    (Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleAssocIso M N P).hom.app U
      ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p) =
        (Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule N P)).app U m ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear N P).app U n p) := by
  have h := congrArg (fun b => b.app U m n p) (tensorModuleAssocIso_trilinear M N P)
  rw [Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv_apply, tensorRightTrilinearEquiv_app_tensor] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorAssociativitySections.Construction
