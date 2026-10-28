import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearFlip
import OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorAssociativity

/-! # Trilinear Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearProducts.Construction

noncomputable section

/-! The two actual composites of bilinear products, encoded as
trilinear sheaf maps. The left composite has its tensor factorization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorAssociativity.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps

universe u

variable {X : Scheme.{u}} {M N P MN NP Q : X.Modules}

def lineBilinearComposeLeft (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N MN) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap MN P Q) :
    Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap M N P Q where
  app U := (b.app U).compr₂ (c.app U)
  naturality h m n p := by
    change Q.presheaf.map h.op (c.app _ (b.app _ m n) p) = _
    rw [c.naturality, b.naturality]
    rfl

def lineBilinearComposeRight (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap N P NP) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M NP Q) :
    Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap M N P Q :=
  (lineBilinearComposeLeft b (BilinearFlip.Construction.flipLineBilinear c)).rotate

theorem lineBilinearComposeLeft_app (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N MN) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap MN P Q)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) :
    (lineBilinearComposeLeft b c).app U m n p = c.app U (b.app U m n) p := rfl

theorem lineBilinearComposeRight_app (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap N P NP) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M NP Q)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) :
    (lineBilinearComposeRight b c).app U m n p = c.app U m (b.app U n p) := rfl

theorem tensorMap_app_tensor (f : M ⟶ MN) (g : N ⟶ NP)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (Picard.PoincareBundle.Tensor.SheafMaps.tensorMap f g).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) =
      (Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear MN NP).app U (f.app U m) (g.app U n) := by
  have h := Picard.PoincareBundle.Tensor.SheafMaps.tensorMap_bilinear f g
  rw [Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear_postcomp] at h
  exact congrArg (fun b => b.app U m n) h

theorem toHom_app_tensor (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) = b.app U m n := by
  have h := (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P).apply_symm_apply b
  rw [Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear_postcomp] at h
  exact congrArg (fun b => b.app U m n) h

theorem lineBilinearComposeLeft_tensor (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N MN) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap MN P Q) :
    Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv M N P Q
      (Picard.PoincareBundle.Tensor.SheafMaps.tensorMap (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b) (𝟙 P) ≫ Picard.PoincareBundle.Bilinear.BilinearPullback.toHom c) =
        lineBilinearComposeLeft b c := by
  ext U m n p
  rw [Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv_apply]
  change (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom c).app U
      ((Picard.PoincareBundle.Tensor.SheafMaps.tensorMap (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b) (𝟙 P)).app U
        ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p)) = _
  rw [tensorMap_app_tensor, toHom_app_tensor, toHom_app_tensor]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearProducts.Construction
