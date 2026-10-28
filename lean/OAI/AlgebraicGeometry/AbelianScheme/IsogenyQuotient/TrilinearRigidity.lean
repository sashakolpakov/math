import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearCompositionPullback
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineHomRigidity

/-! # Trilinear Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearRigidity.Construction

noncomputable section

/-! Origin restriction detects trilinear maps when the tensor of
their three input lines is isomorphic to the output line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

theorem lineTrilinearToHom_pullback {X Y : Scheme.{u}} (p : X ⟶ Y) {M N P Q : Y.Modules}
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N) (hP : Picard.PoincareBundle.Line.Bundles.IsLine P)
    (b : Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap M N P Q) :
    TrilinearPullback.Construction.lineTrilinearToHom (TrilinearPullback.Construction.lineTrilinearPullback p hM hN hP b) =
      (TrilinearPullback.Construction.tensorTriplePullbackIso p M N P hM hN hP).inv ≫ (Scheme.Modules.pullback p).map (TrilinearPullback.Construction.lineTrilinearToHom b) :=
  (Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv _ _ _ _).symm_apply_apply _

theorem lineTrilinear_eq_of_pullback {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p.appTop]
    (L M N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) {Q : Y.Modules} (e : ((L.tensor M).tensor N).sheaf ≅ Q)
    (b c : Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap L.sheaf M.sheaf N.sheaf Q)
    (h : TrilinearPullback.Construction.lineTrilinearPullback p (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine N) b =
      TrilinearPullback.Construction.lineTrilinearPullback p (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine N) c) : b = c := by
  apply (Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv L.sheaf M.sheaf N.sheaf Q).symm.injective
  apply LineHomRigidity.Construction.lineHom_eq_of_pullback p ((L.tensor M).tensor N) e
  have he := congrArg TrilinearPullback.Construction.lineTrilinearToHom h
  rw [lineTrilinearToHom_pullback, lineTrilinearToHom_pullback] at he
  exact (cancel_epi (TrilinearPullback.Construction.tensorTriplePullbackIso p L.sheaf M.sheaf N.sheaf
    (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine N)).inv).mp he

theorem lineTrilinear_eq_of_origin {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
    (L M N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle T.left) {Q : T.left.Modules} (e : ((L.tensor M).tensor N).sheaf ≅ Q)
    (b c : Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap L.sheaf M.sheaf N.sheaf Q)
    (h : TrilinearPullback.Construction.lineTrilinearPullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine N) b =
      TrilinearPullback.Construction.lineTrilinearPullback η[T].left (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine L) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine M) (Poincare.ProductIsomorphisms.Construction.lineBundle_isPoincareBundleLine N) c) : b = c := by
  have : IsIso η[T].left.appTop := Poincare.ProductIsomorphisms.Construction.origin_appTop_isIso T
  exact lineTrilinear_eq_of_pullback η[T].left L M N e b c h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearRigidity.Construction
