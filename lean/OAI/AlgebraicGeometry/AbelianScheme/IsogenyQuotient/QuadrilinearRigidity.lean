import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearCompositionPullback
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineHomRigidity

/-! # Quadrilinear Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearRigidity.Construction

noncomputable section

/-! Restriction to the origin detects four-input maps when the
tensor of the four original input lines is isomorphic to the output. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

theorem lineQuadrilinearToHom_pullback {X Y : Scheme.{u}} (p : X ⟶ Y) {M N P Q R : Y.Modules}
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N)
    (hP : Picard.PoincareBundle.Line.Bundles.IsLine P) (hQ : Picard.PoincareBundle.Line.Bundles.IsLine Q) (b : QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R) :
    TensorQuadrilinear.Construction.lineQuadrilinearToHom (QuadrilinearPullback.Construction.lineQuadrilinearPullback p hM hN hP hQ b) =
      (QuadrilinearPullback.Construction.tensorFourPullbackIso p M N P Q hM hN hP hQ).inv ≫ (Scheme.Modules.pullback p).map (TensorQuadrilinear.Construction.lineQuadrilinearToHom b) :=
  (TensorQuadrilinear.Construction.tensorQuadrilinearEquiv _ _ _ _ _).symm_apply_apply _

theorem lineQuadrilinear_eq_of_pullback {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p.appTop]
    (L M N P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) {R : Y.Modules} (e : (((L.tensor M).tensor N).tensor P).sheaf ≅ R)
    (b c : QuadrilinearProducts.Construction.SheafQuadrilinearMap L.sheaf M.sheaf N.sheaf P.sheaf R)
    (h : QuadrilinearPullback.Construction.lineQuadrilinearPullback p (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M)
        (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine N) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine P) b =
      QuadrilinearPullback.Construction.lineQuadrilinearPullback p (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M)
        (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine N) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine P) c) : b = c := by
  apply (TensorQuadrilinear.Construction.tensorQuadrilinearEquiv L.sheaf M.sheaf N.sheaf P.sheaf R).symm.injective
  apply LineHomRigidity.Construction.lineHom_eq_of_pullback p (((L.tensor M).tensor N).tensor P) e
  have he := congrArg TensorQuadrilinear.Construction.lineQuadrilinearToHom h
  rw [lineQuadrilinearToHom_pullback, lineQuadrilinearToHom_pullback] at he
  exact (cancel_epi (QuadrilinearPullback.Construction.tensorFourPullbackIso p L.sheaf M.sheaf N.sheaf P.sheaf
    (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine N) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine P)).inv).mp he

theorem lineQuadrilinear_eq_of_origin {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
    (L M N P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle T.left) {R : T.left.Modules} (e : (((L.tensor M).tensor N).tensor P).sheaf ≅ R)
    (b c : QuadrilinearProducts.Construction.SheafQuadrilinearMap L.sheaf M.sheaf N.sheaf P.sheaf R)
    (h : QuadrilinearPullback.Construction.lineQuadrilinearPullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M)
        (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine N) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine P) b =
      QuadrilinearPullback.Construction.lineQuadrilinearPullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M)
        (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine N) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine P) c) : b = c := by
  have : IsIso η[T].left.appTop := Poincare.ProductIsomorphisms.Construction.origin_appTop_isIso T
  exact lineQuadrilinear_eq_of_pullback η[T].left L M N P e b c h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearRigidity.Construction
