import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

/-! # Contraction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

noncomputable section

/-!
# Inserting a section into an actual bilinear line-bundle structure map
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

variable {X : Scheme.{u}} {M N P : X.Modules} (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)

/-- Insert a section of the first line into the actual bilinear structure map. -/
def contractLeft : N ⟶ P :=
  (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso N).inv ≫ Tensor.SheafMaps.tensorMap s (𝟙 N) ≫ BilinearPullback.toHom β

/-- Contraction has precisely the defining tensor factorization. -/
theorem contractLeft_fac :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso N).hom ≫ contractLeft β s = Tensor.SheafMaps.tensorMap s (𝟙 N) ≫ BilinearPullback.toHom β := by
  unfold contractLeft
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- On actual sections, contraction evaluates the inserted section at one. -/
theorem contractLeft_app (U : X.Opens) (n : Γ(N, U)) :
    (contractLeft β s).app U n = β.app U (s.app U (1 : Γ(X, U))) n := by
  have h := congrArg (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) N P) (contractLeft_fac β s)
  rw [AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, Tensor.UnitPullback.tensorUnitLeft_bilinear, Tensor.SheafMaps.tensorMap_precomp] at h
  have hβ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P (BilinearPullback.toHom β) = β := (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P).apply_symm_apply β
  rw [hβ] at h
  have he := congrArg (fun b => b.app U (1 : Γ(X, U)) n) h
  change (contractLeft β s).app U ((1 : Γ(X, U)) • n) =
    β.app U (s.app U (1 : Γ(X, U))) n at he
  rw [one_smul] at he
  exact he

/-- Inserting a frame into a bilinear isomorphism gives an actual line-bundle isomorphism. -/
instance contractLeft_isIso [IsIso s] [IsIso (BilinearPullback.toHom β)] : IsIso (contractLeft β s) := by
  unfold contractLeft
  infer_instance

/-- Contraction commutes with postcomposition of the actual structure map. -/
theorem contractLeft_postcomp {Q : X.Modules} (t : P ⟶ Q) :
    contractLeft (β.postcomp t) s = contractLeft β s ≫ t := by
  unfold contractLeft
  rw [BilinearPullback.toHom_postcomp]
  simp only [Category.assoc]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction
