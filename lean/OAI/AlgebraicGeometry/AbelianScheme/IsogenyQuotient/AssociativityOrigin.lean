import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearRigidity

/-! # Associativity Origin -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativityOrigin.Construction

noncomputable section

/-! The associativity equation for line products on a proper smooth
connected group parameter is detected by its actual origin pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

universe u

theorem lineBilinear_associative_of_origin {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
    (L M N LM MN : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle T.left) {Q : T.left.Modules}
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M.sheaf N.sheaf MN.sheaf) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L.sheaf MN.sheaf Q)
    (d : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L.sheaf M.sheaf LM.sheaf) (e : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap LM.sheaf N.sheaf Q)
    [hdIso : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom d)] [heIso : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom e)]
    (h : ∀ (U : (𝟙_ (Over (Spec (.of k)))).left.Opens)
      (l : Γ((Scheme.Modules.pullback η[T].left).obj L.sheaf, U))
      (m : Γ((Scheme.Modules.pullback η[T].left).obj M.sheaf, U))
      (n : Γ((Scheme.Modules.pullback η[T].left).obj N.sheaf, U)),
      (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine MN) c).app U l
        ((Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine N) b).app U m n) =
      (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine LM) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine N) e).app U
        ((Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M) d).app U l m) n)
    (U : T.left.Opens) (l : Γ(L.sheaf, U)) (m : Γ(M.sheaf, U)) (n : Γ(N.sheaf, U)) :
    c.app U l (b.app U m n) = e.app U (d.app U l m) n := by
  have hIso : IsIso (TrilinearPullback.Construction.lineTrilinearToHom (TrilinearProducts.Construction.lineBilinearComposeLeft d e)) :=
    @TrilinearCompositionPullback.Construction.lineTrilinearToHom_composeLeft_isIso T.left L.sheaf M.sheaf N.sheaf LM.sheaf Q d e hdIso heIso
  let et : ((L.tensor M).tensor N).sheaf ≅ Q :=
    @asIso T.left.Modules inferInstance _ _ (TrilinearPullback.Construction.lineTrilinearToHom (TrilinearProducts.Construction.lineBilinearComposeLeft d e)) hIso
  have he : TrilinearProducts.Construction.lineBilinearComposeRight b c = TrilinearProducts.Construction.lineBilinearComposeLeft d e := by
    apply TrilinearRigidity.Construction.lineTrilinear_eq_of_origin T L M N et
    rw [TrilinearCompositionPullback.Construction.lineBilinearComposeRight_pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M)
        (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine N) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine MN),
      TrilinearCompositionPullback.Construction.lineBilinearComposeLeft_pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M)
        (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine N) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine LM)]
    ext V x y z
    exact h V x y z
  exact congrArg (fun b => b.app U l m n) he

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativityOrigin.Construction
