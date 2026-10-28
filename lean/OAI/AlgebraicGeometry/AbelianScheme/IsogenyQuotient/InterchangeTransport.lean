import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.InterchangeTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.TransportComposition

/-! # Interchange Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeTransport.Construction

noncomputable section

/-! Consistent changes of all nine fibers reflect the actual
biextension interchange equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport

universe u

theorem lineBilinear_interchange_of_transport {S : Scheme.{u}}
    {C A B X CA CB AX BX W C' A' B' X' CA' CB' AX' BX' W' : S.Modules}
    (ax : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap A X AX) (bx : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap B X BX)
    (cb : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap C B CB) (ca : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap C A CA)
    (byMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap CB AX W) (az : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap CA BX W)
    (ec : C ≅ C') (ea : A ≅ A') (eb : B ≅ B') (ex : X ≅ X')
    (eca : CA ≅ CA') (ecb : CB ≅ CB') (eax : AX ≅ AX') (ebx : BX ≅ BX') (ew : W ≅ W')
    (h : ∀ (U : S.Opens) (c : Γ(C', U)) (a : Γ(A', U)) (b : Γ(B', U)) (x : Γ(X', U)),
      (Picard.PoincareBundle.Bilinear.Transport.transport byMap ecb eax ew).app U ((Picard.PoincareBundle.Bilinear.Transport.transport cb ec eb ecb).app U c b)
        ((Picard.PoincareBundle.Bilinear.Transport.transport ax ea ex eax).app U a x) =
      (Picard.PoincareBundle.Bilinear.Transport.transport az eca ebx ew).app U ((Picard.PoincareBundle.Bilinear.Transport.transport ca ec ea eca).app U c a)
        ((Picard.PoincareBundle.Bilinear.Transport.transport bx eb ex ebx).app U b x))
    (U : S.Opens) (c : Γ(C, U)) (a : Γ(A, U)) (b : Γ(B, U)) (x : Γ(X, U)) :
    byMap.app U (cb.app U c b) (ax.app U a x) = az.app U (ca.app U c a) (bx.app U b x) := by
  have hr := Picard.PoincareBundle.Bilinear.InterchangeTransport.interchange
    (Picard.PoincareBundle.Bilinear.Transport.transport ax ea ex eax) (Picard.PoincareBundle.Bilinear.Transport.transport bx eb ex ebx)
    (Picard.PoincareBundle.Bilinear.Transport.transport cb ec eb ecb) (Picard.PoincareBundle.Bilinear.Transport.transport ca ec ea eca)
    (Picard.PoincareBundle.Bilinear.Transport.transport byMap ecb eax ew) (Picard.PoincareBundle.Bilinear.Transport.transport az eca ebx ew)
    ec.symm ea.symm eb.symm ex.symm eca.symm ecb.symm eax.symm ebx.symm ew.symm h U c a b x
  simpa only [Picard.PoincareBundle.Bilinear.TransportComposition.transport_trans, Iso.self_symm_id,
    Picard.PoincareBundle.Bilinear.TransportComposition.transport_refl] using hr

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeTransport.Construction
