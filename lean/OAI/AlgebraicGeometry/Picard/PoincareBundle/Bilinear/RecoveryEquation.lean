import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.AlgebraTransport

/-! # Recovery Equation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.RecoveryEquation

noncomputable section

/-!
# A genuine sheaf recovery equation recovers the full bilinear operation
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M N P : Y.Modules} {A B C : X.Modules}
  (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
  (δ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap A B C)
  (a : (Scheme.Modules.pullback f).obj M ⟶ A) (b : (Scheme.Modules.pullback f).obj N ⟶ B)
  (c : (Scheme.Modules.pullback f).obj P ⟶ C)
  (h : (Scheme.Modules.pullback f).map (BilinearPullback.toHom δ) ≫ c =
    (Tensor.LinePullback.pullbackIso f M N hM hN).hom ≫ Tensor.SheafMaps.tensorMap a b ≫ BilinearPullback.toHom β)

include h in
/-- The exact represented sheaf-map recovery is the full bilinear recovery equation. -/
theorem recovery_bilinear : (BilinearPullback.pullback f hM hN δ).postcomp c = β.precomp a b := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm.injective
  change BilinearPullback.toHom _ = BilinearPullback.toHom _
  rw [BilinearPullback.toHom_postcomp, BilinearPullback.toHom_precomp, BilinearPullback.toHom_pullback]
  apply (cancel_epi (Tensor.LinePullback.pullbackIso f M N hM hN).hom).mp
  rw [← Category.assoc, BilinearPullback.pulledHom_fac]
  exact h

variable (eM : (Scheme.Modules.pullback f).obj M ≅ A) (eN : (Scheme.Modules.pullback f).obj N ≅ B)
  (eP : (Scheme.Modules.pullback f).obj P ≅ C)
  (he : (Scheme.Modules.pullback f).map (BilinearPullback.toHom δ) ≫ eP.hom =
    (Tensor.LinePullback.pullbackIso f M N hM hN).hom ≫ Tensor.SheafMaps.tensorMap eM.hom eN.hom ≫ BilinearPullback.toHom β)

include he in
/-- The recovered bilinear operation is precisely the original operation after the three genuine line comparisons. -/
theorem recovery_transport : Transport.transport (BilinearPullback.pullback f hM hN δ) eM eN eP = β := by
  have hb := recovery_bilinear f hM hN δ β eM.hom eN.hom eP.hom he
  apply AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro n
  have hv := congrArg (fun γ => γ.app U (eM.inv.app U m) (eN.inv.app U n)) hb
  change (Transport.transport (BilinearPullback.pullback f hM hN δ) eM eN eP).app U m n =
    β.app U (eM.hom.app U (eM.inv.app U m)) (eN.hom.app U (eN.inv.app U n)) at hv
  have hm : eM.hom.app U (eM.inv.app U m) = m :=
    AlgebraTransport.inv_hom_app eM.symm U m
  have hn : eN.hom.app U (eN.inv.app U n) = n :=
    AlgebraTransport.inv_hom_app eN.symm U n
  exact hv.trans (congrArg₂ (fun x y => β.app U x y) hm hn)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.RecoveryEquation
