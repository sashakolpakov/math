import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearRigidity

/-! # Interchange Origin -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeOrigin.Construction

noncomputable section

/-! The actual biextension interchange equation is detected at the
origin of a proper smooth connected group parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

universe u

theorem lineBilinear_interchange_of_origin {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
    (C A B X CA CB AX BX : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle T.left) {W : T.left.Modules}
    (ax : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap A.sheaf X.sheaf AX.sheaf) (bx : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap B.sheaf X.sheaf BX.sheaf)
    (cb : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap C.sheaf B.sheaf CB.sheaf) (ca : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap C.sheaf A.sheaf CA.sheaf)
    (byMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap CB.sheaf AX.sheaf W) (az : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap CA.sheaf BX.sheaf W)
    [hcaIso : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom ca)] [hbxIso : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom bx)] [hazIso : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom az)]
    (h : ∀ (U : (𝟙_ (Over (Spec (.of k)))).left.Opens)
      (c : Γ((Scheme.Modules.pullback η[T].left).obj C.sheaf, U))
      (a : Γ((Scheme.Modules.pullback η[T].left).obj A.sheaf, U))
      (b : Γ((Scheme.Modules.pullback η[T].left).obj B.sheaf, U))
      (x : Γ((Scheme.Modules.pullback η[T].left).obj X.sheaf, U)),
      (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine CB) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine AX) byMap).app U
        ((Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine C) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine B) cb).app U c b)
        ((Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine A) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine X) ax).app U a x) =
      (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine CA) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine BX) az).app U
        ((Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine C) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine A) ca).app U c a)
        ((Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine B) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine X) bx).app U b x))
    (U : T.left.Opens) (c : Γ(C.sheaf, U)) (a : Γ(A.sheaf, U)) (b : Γ(B.sheaf, U)) (x : Γ(X.sheaf, U)) :
    byMap.app U (cb.app U c b) (ax.app U a x) = az.app U (ca.app U c a) (bx.app U b x) := by
  have hIso : IsIso (TensorQuadrilinear.Construction.lineQuadrilinearToHom (QuadrilinearProducts.Construction.linePairBilinearCompose ca bx az)) :=
    @TensorQuadrilinear.Construction.lineQuadrilinearToHom_pairCompose_isIso T.left C.sheaf A.sheaf B.sheaf X.sheaf
      CA.sheaf BX.sheaf W ca bx az hcaIso hbxIso hazIso
  let et : (((C.tensor A).tensor B).tensor X).sheaf ≅ W :=
    @asIso T.left.Modules inferInstance _ _ (TensorQuadrilinear.Construction.lineQuadrilinearToHom (QuadrilinearProducts.Construction.linePairBilinearCompose ca bx az)) hIso
  have he : (QuadrilinearProducts.Construction.linePairBilinearCompose cb ax byMap).swapMiddle = QuadrilinearProducts.Construction.linePairBilinearCompose ca bx az := by
    apply QuadrilinearRigidity.Construction.lineQuadrilinear_eq_of_origin T C A B X et
    rw [QuadrilinearCompositionPullback.Construction.lineQuadrilinearPullback_swapMiddle η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine C) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine B)
        (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine A) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine X),
      QuadrilinearCompositionPullback.Construction.linePairBilinearCompose_pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine C) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine B)
        (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine A) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine X) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine CB) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine AX),
      QuadrilinearCompositionPullback.Construction.linePairBilinearCompose_pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine C) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine A)
        (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine B) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine X) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine CA) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine BX)]
    ext V c a b x
    exact h V c a b x
  exact congrArg (fun t => t.app U c a b x) he

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeOrigin.Construction
