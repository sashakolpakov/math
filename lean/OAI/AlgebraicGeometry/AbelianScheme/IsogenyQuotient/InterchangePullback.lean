import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearCompositionPullback

/-! # Interchange Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangePullback.Construction

noncomputable section

/-! The actual interchange equation of six bilinear line maps is
preserved by arbitrary geometric pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

universe u

theorem lineBilinear_interchange_pullback {S T : Scheme.{u}} (f : T ⟶ S)
    {C A B X CA CB AX BX W : S.Modules}
    (hC : Picard.PoincareBundle.Line.Bundles.IsLine C) (hA : Picard.PoincareBundle.Line.Bundles.IsLine A)
    (hB : Picard.PoincareBundle.Line.Bundles.IsLine B) (hX : Picard.PoincareBundle.Line.Bundles.IsLine X)
    (hCA : Picard.PoincareBundle.Line.Bundles.IsLine CA) (hCB : Picard.PoincareBundle.Line.Bundles.IsLine CB)
    (hAX : Picard.PoincareBundle.Line.Bundles.IsLine AX) (hBX : Picard.PoincareBundle.Line.Bundles.IsLine BX)
    (ax : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap A X AX) (bx : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap B X BX)
    (cb : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap C B CB) (ca : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap C A CA)
    (byMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap CB AX W) (az : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap CA BX W)
    (h : ∀ (U : S.Opens) (c : Γ(C, U)) (a : Γ(A, U)) (b : Γ(B, U)) (x : Γ(X, U)),
      byMap.app U (cb.app U c b) (ax.app U a x) = az.app U (ca.app U c a) (bx.app U b x))
    (U : T.Opens) (c : Γ((Scheme.Modules.pullback f).obj C, U)) (a : Γ((Scheme.Modules.pullback f).obj A, U))
    (b : Γ((Scheme.Modules.pullback f).obj B, U)) (x : Γ((Scheme.Modules.pullback f).obj X, U)) :
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hCB hAX byMap).app U ((Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hC hB cb).app U c b) ((Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hA hX ax).app U a x) =
      (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hCA hBX az).app U ((Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hC hA ca).app U c a) ((Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hB hX bx).app U b x) := by
  have he : (QuadrilinearProducts.Construction.linePairBilinearCompose cb ax byMap).swapMiddle = QuadrilinearProducts.Construction.linePairBilinearCompose ca bx az := by
    ext V c a b x
    exact h V c a b x
  have hp := congrArg (QuadrilinearPullback.Construction.lineQuadrilinearPullback f hC hA hB hX) he
  rw [QuadrilinearCompositionPullback.Construction.lineQuadrilinearPullback_swapMiddle f hC hB hA hX,
    QuadrilinearCompositionPullback.Construction.linePairBilinearCompose_pullback f hC hB hA hX hCB hAX,
    QuadrilinearCompositionPullback.Construction.linePairBilinearCompose_pullback f hC hA hB hX hCA hBX] at hp
  exact congrArg (fun t => t.app U c a b x) hp

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangePullback.Construction
