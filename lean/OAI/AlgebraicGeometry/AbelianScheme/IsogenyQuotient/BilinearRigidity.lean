import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BilinearProducts

/-! # Bilinear Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearRigidity.Construction

noncomputable section

/-! Normalized invertible products of line sheaves are determined by
their pullback wherever global functions are unchanged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem lineBilinear_eq_of_pullback {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p.appTop]
    (L M N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (b c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L.sheaf M.sheaf N.sheaf)
    [IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b)] [IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom c)]
    (h : Picard.PoincareBundle.Bilinear.BilinearPullback.pullback p (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M) b =
      Picard.PoincareBundle.Bilinear.BilinearPullback.pullback p (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M) c) :
    b = c := by
  have hp := congrArg Picard.PoincareBundle.Bilinear.BilinearPullback.toHom h
  rw [Picard.PoincareBundle.Bilinear.BilinearPullback.toHom_pullback, Picard.PoincareBundle.Bilinear.BilinearPullback.toHom_pullback] at hp
  have hh : (Scheme.Modules.pullback p).map (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b) =
      (Scheme.Modules.pullback p).map (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom c) := by
    apply (cancel_epi (Picard.PoincareBundle.Tensor.LinePullback.pullbackIso p L.sheaf M.sheaf
      (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M)).inv).mp
    exact hp
  have he : asIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b) = asIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom c) :=
    Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.iso_unique p (L.tensor M) N _ _ (by
      apply Iso.ext
      exact hh)
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm.injective
  exact congrArg Iso.hom he

theorem lineBilinear_eq_of_origin {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
    (L M N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle T.left) (b c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L.sheaf M.sheaf N.sheaf)
    [IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b)] [IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom c)]
    (h : Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M) b =
      Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M) c) :
    b = c := by
  have : IsIso η[T].left.appTop := Poincare.ProductIsomorphisms.Construction.origin_appTop_isIso T
  exact lineBilinear_eq_of_pullback η[T].left L M N b c h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearRigidity.Construction
