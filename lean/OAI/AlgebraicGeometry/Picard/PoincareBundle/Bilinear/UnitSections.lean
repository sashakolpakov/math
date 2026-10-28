import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.FrameProducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSections

/-! # Unit Sections -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.UnitSections

noncomputable section

/-! Products of arbitrary line sections are equalities of actual tensor-section maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSections OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

variable {X : Scheme.{u}} {L M N : X.Modules} (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L M N)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (v : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N)
  (h : ∀ U : X.Opens, β.app U (s.app U (1 : Γ(X, U))) (t.app U (1 : Γ(X, U))) =
    v.app U (1 : Γ(X, U)))

include h

/-- The product equation at one determines the entire bilinear map out of the structure module. -/
theorem precomp_eq : β.precomp s t = (Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).postcomp v := by
  apply AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply LinearMap.ext
  intro r
  apply LinearMap.ext
  intro q
  change Γ(X, U) at r q
  change β.app U (s.app U r) (t.app U q) = v.app U (r * q)
  rw [Line.FrameUnits.unit_hom_app s, Line.FrameUnits.unit_hom_app t, Line.FrameUnits.unit_hom_app v]
  erw [(β.app U).map_smul r (s.app U (1 : Γ(X, U))), LinearMap.smul_apply,
    (β.app U (s.app U (1 : Γ(X, U)))).map_smul q (t.app U (1 : Γ(X, U))), h U, smul_smul]

/-- A sectionwise product is exactly the corresponding composite tensor-section morphism. -/
theorem product_eq : AbelianModuli.HilbertConstruction.Tensor.ProductSections.tensorProductSection s t ≫ BilinearPullback.toHom β = v := by
  apply (cancel_epi (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom).mp
  simp only [AbelianModuli.HilbertConstruction.Tensor.ProductSections.tensorProductSection, Category.assoc, Iso.hom_inv_id_assoc]
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) N).injective
  rw [AbelianModuli.HilbertConstruction.Tensor.PullbackComparison.tensorHomEquiv_precomp, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, Tensor.UnitPullback.tensorUnitLeft_bilinear]
  have hβ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv L M N (BilinearPullback.toHom β) = β :=
    (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv L M N).apply_symm_apply β
  rw [hβ]
  exact precomp_eq β s t v h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.UnitSections
