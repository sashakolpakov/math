import OAI.RepresentationTheory.Theta.Geometric.Geometry
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components

/-! # Component Projector Maps -/

namespace OAI.RepresentationTheory.Theta.Geometric.ComponentProjectorMaps

noncomputable section

/-! The actual product-coordinate projector retains precisely its own
component Albanese map and kills the remaining component maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {B : Scheme} {T : Over B} {r : ℕ} (C : AlgebraicGeometry.PELModuli.IntegralModel.Components.ComponentAlbaneseData T r)

theorem componentComparison_inverse_projection (j : Fin r) :
    (AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProductComparison C.A).inv ≫ AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProductProjection C.A j =
      Pi.π (fun k => (C.A k).X) j := by
  rw [← AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProductComparison_projection, Iso.inv_hom_id_assoc]

theorem componentProductMap_projector (i j : Fin r) :
    (C.componentProductMap i ≫ (AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProductComparison C.A).inv) ≫
      Geometry.productCoordinateIdempotent C.A j =
    if i = j then C.componentProductMap i ≫ (AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProductComparison C.A).inv else 1 := by
  apply (cancel_mono (AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProductComparison C.A).hom).mp
  rw [Geometry.productCoordinateIdempotent]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  apply Pi.hom_ext
  intro k
  by_cases hij : i = j
  · subst i
    by_cases hkj : k = j
    · subst k
      simp only [ite_true, Category.assoc, Pi.lift_comp_π, AlgebraicGeometry.PELModuli.IntegralModel.Components.ComponentAlbaneseData.componentProductMap]
      simp only [Iso.inv_hom_id_assoc, Pi.lift_comp_π, AlgebraicGeometry.PELModuli.IntegralModel.Components.ComponentAlbaneseData.coordinateMap_self]
    · have hjk : j ≠ k := Ne.symm hkj
      simp [hkj, AlgebraicGeometry.PELModuli.IntegralModel.Components.ComponentAlbaneseData.componentProductMap, C.coordinateMap_ne j k hjk]
  · by_cases hkj : k = j
    · subst k
      simp [hij, AlgebraicGeometry.PELModuli.IntegralModel.Components.ComponentAlbaneseData.componentProductMap, C.coordinateMap_ne i j hij]
    · simp [hij, hkj]

end

end OAI.RepresentationTheory.Theta.Geometric.ComponentProjectorMaps
