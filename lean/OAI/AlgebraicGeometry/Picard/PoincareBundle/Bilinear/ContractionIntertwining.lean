import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrMapComparison

/-! # Contraction Intertwining -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionIntertwining

noncomputable section

/-! Inserting corresponding sections into intertwined actual bilinear formulas preserves the comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps

variable {X : Scheme.{u}} {M N P M' N' P' : X.Modules}
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (γ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M' N' P')
  (a : M ≅ M') (b : N ≅ N') (c : P ≅ P')
  (he : BilinearPullback.toHom β ≫ c.hom = (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b).hom ≫ BilinearPullback.toHom γ)

include he

theorem transported_eq : Transport.transport β a b c = γ := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M' N' P').symm.injective
  change BilinearPullback.toHom (Transport.transport β a b c) = BilinearPullback.toHom γ
  rw [Transport.toHom_transport, he, Tensor.CongrMapComparison.congr_hom,
    ← Category.assoc, Tensor.SheafMaps.tensorMap_comp, a.inv_hom_id, b.inv_hom_id, Tensor.SheafMaps.tensorMap_id, Category.id_comp]

/-- Equality of the actual tensor formulas and inserted sections gives equality of the contracted maps. -/
theorem contraction (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (s' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M')
    (hs : s ≫ a.hom = s') :
    Contraction.contractLeft β s ≫ c.hom = b.hom ≫ Contraction.contractLeft γ s' := by
  have ht := Transport.contractLeft_transport β a b c s
  have hh := (congrArg₂ Contraction.contractLeft (transported_eq β γ a b c he) hs).symm.trans ht
  have hb := congrArg (fun e => b.hom ≫ e) hh
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hb.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionIntertwining
