import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.AlgebraTransport

/-! # Interchange Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.InterchangeTransport

noncomputable section

/-!
# Actual biextension interchange is preserved by consistent changes of its nine line fibers
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.AlgebraTransport

variable {S : Scheme.{u}}

/-- The six genuine bilinear maps in an interchange square remain compatible after fiber transport. -/
theorem interchange {C A B X CA CB AX BX W C' A' B' X' CA' CB' AX' BX' W' : S.Modules}
    (ax : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap A X AX) (bx : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap B X BX)
    (cb : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap C B CB) (ca : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap C A CA)
    (byMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap CB AX W) (az : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap CA BX W)
    (ec : C ≅ C') (ea : A ≅ A') (eb : B ≅ B') (ex : X ≅ X')
    (eca : CA ≅ CA') (ecb : CB ≅ CB') (eax : AX ≅ AX') (ebx : BX ≅ BX') (ew : W ≅ W')
    (h : ∀ (U : S.Opens) (c : Γ(C, U)) (a : Γ(A, U)) (b : Γ(B, U)) (x : Γ(X, U)),
      byMap.app U (cb.app U c b) (ax.app U a x) = az.app U (ca.app U c a) (bx.app U b x))
    (U : S.Opens) (c : Γ(C', U)) (a : Γ(A', U)) (b : Γ(B', U)) (x : Γ(X', U)) :
    (Transport.transport byMap ecb eax ew).app U ((Transport.transport cb ec eb ecb).app U c b)
      ((Transport.transport ax ea ex eax).app U a x) =
      (Transport.transport az eca ebx ew).app U ((Transport.transport ca ec ea eca).app U c a)
        ((Transport.transport bx eb ex ebx).app U b x) := by
  change ew.hom.app U (byMap.app U
      (ecb.inv.app U (ecb.hom.app U (cb.app U (ec.inv.app U c) (eb.inv.app U b))))
      (eax.inv.app U (eax.hom.app U (ax.app U (ea.inv.app U a) (ex.inv.app U x))))) =
    ew.hom.app U (az.app U
      (eca.inv.app U (eca.hom.app U (ca.app U (ec.inv.app U c) (ea.inv.app U a))))
      (ebx.inv.app U (ebx.hom.app U (bx.app U (eb.inv.app U b) (ex.inv.app U x)))))
  rw [AlgebraTransport.inv_hom_app, AlgebraTransport.inv_hom_app, AlgebraTransport.inv_hom_app, AlgebraTransport.inv_hom_app, h]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.InterchangeTransport
