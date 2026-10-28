import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrMapComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport

/-! # Equivariant Line Contraction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.EquivariantLineContraction

noncomputable section

/-! Inserting an equivariant line section into an actual equivariant bilinear formula preserves equivariance. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps

variable {X : Scheme.{u}} (g : X ⟶ X) {M N P : X.Modules}
  (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P)
  (a : (Scheme.Modules.pullback g).obj M ≅ M)
  (b : (Scheme.Modules.pullback g).obj N ≅ N)
  (c : (Scheme.Modules.pullback g).obj P ≅ P)
  (he : (Scheme.Modules.pullback g).map (Bilinear.BilinearPullback.toHom β) ≫ c.hom =
    (Tensor.LinePullback.pullbackIso g M N hM hN).hom ≫ (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b).hom ≫ Bilinear.BilinearPullback.toHom β)

include he

/-- Equivariance of the genuine tensor morphism gives equivariance of its bilinear section formula. -/
theorem transport_eq : Bilinear.Transport.transport (Bilinear.BilinearPullback.pullback g hM hN β) a b c = β := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P).symm.injective
  change Bilinear.BilinearPullback.toHom (Bilinear.Transport.transport (Bilinear.BilinearPullback.pullback g hM hN β) a b c) = Bilinear.BilinearPullback.toHom β
  have hh := he
  rw [Tensor.CongrMapComparison.congr_hom] at hh
  rw [Bilinear.Transport.toHom_transport, Bilinear.BilinearPullback.toHom_pullback]
  unfold Bilinear.BilinearPullback.pulledHom
  simp only [Category.assoc]
  rw [hh, Iso.inv_hom_id_assoc, ← Category.assoc, Tensor.SheafMaps.tensorMap_comp,
    a.inv_hom_id, b.inv_hom_id, Tensor.SheafMaps.tensorMap_id, Category.id_comp]

/-- An equivariant section may be inserted without losing the symmetry of the actual line formula. -/
theorem contraction_equivariant (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (hs : Bilinear.ContractionPullback.pulledSection g s ≫ a.hom = s) :
    (Scheme.Modules.pullback g).map (Bilinear.Contraction.contractLeft β s) ≫ c.hom = b.hom ≫ Bilinear.Contraction.contractLeft β s := by
  have hp := Bilinear.Transport.contractLeft_pullback_transport g hM hN β a b c s
  have hβ := transport_eq g hM hN β a b c he
  have h := (congrArg₂ Bilinear.Contraction.contractLeft hβ hs).symm.trans hp
  have hb := congrArg (fun q => b.hom ≫ q) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hb.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.EquivariantLineContraction
