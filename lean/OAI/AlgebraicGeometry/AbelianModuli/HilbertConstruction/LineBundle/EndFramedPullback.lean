import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.EndTransferCompatibility

/-! # End Framed Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The global scalar transfer agrees with every frame after arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem Line.Bundles.LineBundle.endTransfer_framed_pullback (L : Line.Bundles.LineBundle Y) (f : X ⟶ Y) (φ : End L.sheaf)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf) :
    (Scheme.Modules.pullback f).map (L.endTransfer φ) = Local.LineBundleEndTransfer.localLineEndTransfer f φ e := by
  let U : LineBundle.EndGluing.LineEndFrameOpen L → X.Opens := fun i => f ⁻¹ᵁ i.openSet
  have hU : ∀ x : X, ∃ i, x ∈ U i := fun x => LineBundle.EndGluing.lineEndFrameCover_covers L (f x)
  apply Module.MapCoverEquality.moduleMap_eq_of_pullback_cover U hU
  intro i
  change (Scheme.Modules.pullback (f ⁻¹ᵁ i.openSet).ι).map
      ((Scheme.Modules.pullback f).map (L.endTransfer φ)) =
    (Scheme.Modules.pullback (f ⁻¹ᵁ i.openSet).ι).map (Local.LineBundleEndTransfer.localLineEndTransfer f φ e)
  apply Local.EndTransferCompatibility.localLineEndTransfer_map_of_comp (f ⁻¹ᵁ i.openSet).ι f (L.endTransfer φ) φ e
  exact Local.EndTransferCompatibility.localLineEndTransfer_map_congr (morphismRestrict_ι f i.openSet) (L.endTransfer φ) φ
    (Local.TensorPowerValues.refinedPullbackFrame (f ∣_ i.openSet) i.openSet.ι i.frame)
    (Local.TensorPowerValues.refinedPullbackFrame (f ⁻¹ᵁ i.openSet).ι f e)
    (Local.EndTransferCompatibility.localLineEndTransfer_map_comp (f ∣_ i.openSet) i.openSet.ι (L.endTransfer φ) φ i.frame
      (L.endTransfer_pullback φ i))

theorem Line.Bundles.LineBundle.endScalar_framed_pullback (L : Line.Bundles.LineBundle Y) (f : X ⟶ Y) (φ : End L.sheaf)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf) :
    f.appTop (L.endScalar φ) =
      Frame.Coordinates.structureModuleEndValue X (LineBundle.EndScalars.framedEndScalar e ((Scheme.Modules.pullback f).map φ)) := by
  rw [Line.Bundles.LineBundle.endScalar, ← Scalar.BaseChange.structureModuleEndValue_baseChange, L.endTransfer_framed_pullback f φ e]
  simp only [Local.LineBundleEndTransfer.localLineEndTransfer, Frame.EndTransfer.frameTransferEnd, Iso.symm_inv, Iso.symm_hom,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
