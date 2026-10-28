import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearCurry

/-! # Tensor Quadrilinear -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorQuadrilinear.Construction

noncomputable section

/-! The four-input tensor universal property and the invertible
tensor map underlying a pair of bilinear products followed by a third. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps

universe u

variable {X : Scheme.{u}} {M N P Q MN PQ R : X.Modules}

def tensorQuadrilinearEquiv (M N P Q R : X.Modules) :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q ⟶ R) ≃ QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R :=
  (Picard.Homomorphisms.TensorHom.Construction.tensorInternalHomEquiv (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q R).trans
    ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv M N P (Picard.Homomorphisms.InternalHom.Construction.moduleInternalHom Q R)).trans QuadrilinearCurry.Construction.trilinearHomQuadrilinearEquiv)

theorem tensorQuadrilinearEquiv_apply (f : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q ⟶ R)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) (q : Γ(Q, U)) :
    (tensorQuadrilinearEquiv M N P Q R f).app U m n p q =
      f.app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q).app U
        ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p) q) := by
  change Picard.Homomorphisms.TensorHom.Construction.internalHomEval Q R U
    ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv M N P (Picard.Homomorphisms.InternalHom.Construction.moduleInternalHom Q R)
      (Picard.Homomorphisms.TensorHom.Construction.sheafBilinearCurry (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q R f))).app U m n p) q = _
  rw [Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv_apply]
  change (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q R f).app U
    ((AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).presheaf.map (𝟙 U).op
      ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p)) q = _
  rw [op_id, (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).presheaf.map_id, AddCommGrpCat.id_apply,
    Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear_postcomp]
  rfl

def lineQuadrilinearToHom (b : QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q ⟶ R :=
  (tensorQuadrilinearEquiv M N P Q R).symm b

theorem lineQuadrilinearToHom_app_tensor (b : QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) (q : Γ(Q, U)) :
    (lineQuadrilinearToHom b).app U
      ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q).app U
        ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p) q) =
      b.app U m n p q := by
  rw [← tensorQuadrilinearEquiv_apply]
  exact congrArg (fun b => b.app U m n p q) ((tensorQuadrilinearEquiv M N P Q R).apply_symm_apply b)

theorem linePairBilinearCompose_tensor (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N MN) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap P Q PQ)
    (d : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap MN PQ R) :
    tensorQuadrilinearEquiv M N P Q R
      ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleAssocIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P Q).hom ≫ Picard.PoincareBundle.Tensor.SheafMaps.tensorMap (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b) (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom c) ≫ Picard.PoincareBundle.Bilinear.BilinearPullback.toHom d) =
        QuadrilinearProducts.Construction.linePairBilinearCompose b c d := by
  ext U m n p q
  rw [tensorQuadrilinearEquiv_apply]
  change (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom d).app U ((Picard.PoincareBundle.Tensor.SheafMaps.tensorMap (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b) (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom c)).app U
    ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleAssocIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P Q).hom.app U
      ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q).app U
        ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p) q))) = _
  rw [TensorAssociativitySections.Construction.tensorModuleAssocIso_app_tensor, TrilinearProducts.Construction.tensorMap_app_tensor,
    TrilinearProducts.Construction.toHom_app_tensor, TrilinearProducts.Construction.toHom_app_tensor, TrilinearProducts.Construction.toHom_app_tensor]
  rfl

theorem lineQuadrilinearToHom_pairCompose (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N MN) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap P Q PQ)
    (d : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap MN PQ R) :
    lineQuadrilinearToHom (QuadrilinearProducts.Construction.linePairBilinearCompose b c d) =
      (Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleAssocIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P Q).hom ≫ Picard.PoincareBundle.Tensor.SheafMaps.tensorMap (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b) (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom c) ≫ Picard.PoincareBundle.Bilinear.BilinearPullback.toHom d := by
  rw [lineQuadrilinearToHom, ← linePairBilinearCompose_tensor b c d, Equiv.symm_apply_apply]

instance lineQuadrilinearToHom_pairCompose_isIso (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N MN) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap P Q PQ)
    (d : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap MN PQ R) [IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b)] [IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom c)] [IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom d)] :
    IsIso (lineQuadrilinearToHom (QuadrilinearProducts.Construction.linePairBilinearCompose b c d)) := by
  rw [lineQuadrilinearToHom_pairCompose]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorQuadrilinear.Construction
