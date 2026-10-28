import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BilinearProducts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.TransportComposition

/-! # Fiber Product Origin -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberProductOrigin.Construction

noncomputable section

/-! Canonical fiber comparisons turn a normalized pullback product
into multiplication in the specified point frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

universe u

theorem fiberPullbackIso_eq_comparison {S : Scheme.{u}} {E T U : Over S}
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (r : U ⟶ T) (x : T ⟶ E) (x' : U ⟶ E) (hx : r ≫ x = x') :
    Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r x x' hx = Picard.PoincareBundle.GlobalPullbackFrame.comparison x L r x' hx := by
  have h := Picard.PoincareBundle.GlobalPullbackFrame.comparison_eq x L r x' hx
  simpa only [Picard.PoincareBundle.Line.Fibers.fiberPullbackIso, Picard.PoincareBundle.Line.Fibers.fiber, NatIso.trans_app] using h.symm

theorem framedLineProduct_transport {X : Scheme.{u}} {M N P M' N' P' : X.Modules}
    (l : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (m : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N) (n : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ P)
    (a : M ≅ M') (b : N ≅ N') (c : P ≅ P') :
    Picard.PoincareBundle.Bilinear.Transport.transport (IsogenyQuotient.Poincare.BilinearProducts.Construction.framedLineProduct l m n) a b c =
      IsogenyQuotient.Poincare.BilinearProducts.Construction.framedLineProduct (l ≪≫ a) (m ≪≫ b) (n ≪≫ c) :=
  Picard.PoincareBundle.Bilinear.TransportComposition.transport_trans _ l m n a b c

theorem pullBilinear_of_framed_pullback {S : Scheme.{u}} {E T U : Over S}
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (r : U ⟶ T)
    (x y z : T ⟶ E) (x' y' z' : U ⟶ E) (hx : r ≫ x = x') (hy : r ≫ y = y') (hz : r ≫ z = z')
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L y) (Picard.PoincareBundle.Line.Fibers.fiber L z))
    (l : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.left ≅ (Scheme.Modules.pullback r.left).obj (Picard.PoincareBundle.Line.Fibers.fiber L x))
    (m : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.left ≅ (Scheme.Modules.pullback r.left).obj (Picard.PoincareBundle.Line.Fibers.fiber L y))
    (n : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.left ≅ (Scheme.Modules.pullback r.left).obj (Picard.PoincareBundle.Line.Fibers.fiber L z))
    (l' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L x') (m' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L y')
    (n' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L z')
    (hl : l ≪≫ Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r x x' hx = l') (hm : m ≪≫ Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r y y' hy = m')
    (hn : n ≪≫ Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r z z' hz = n')
    (hb : Picard.PoincareBundle.Bilinear.BilinearPullback.pullback r.left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L y) b =
      IsogenyQuotient.Poincare.BilinearProducts.Construction.framedLineProduct l m n) :
    Picard.PoincareBundle.Line.Fibers.pullBilinear L r x y z x' y' z' hx hy hz b = IsogenyQuotient.Poincare.BilinearProducts.Construction.framedLineProduct l' m' n' := by
  unfold Picard.PoincareBundle.Line.Fibers.pullBilinear
  rw [hb, framedLineProduct_transport, hl, hm, hn]

variable {k : Type} [Field k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))} [GrpObj T]

theorem poincarePointOriginFrame_comparison (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme)
    [IsMonHom t] [IsMonHom a] (h : η[T] ≫ lift t a = 1) :
    IsogenyQuotient.Poincare.OriginFrames.Construction.poincarePointOriginFrame D t a ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] (lift t a) 1 h = IsogenyQuotient.Poincare.OriginFrames.Construction.poincareZeroFrame D _ := by
  unfold IsogenyQuotient.Poincare.OriginFrames.Construction.poincarePointOriginFrame
  rw [fiberPullbackIso_eq_comparison]
  change (IsogenyQuotient.Poincare.OriginFrames.Construction.poincareZeroFrame D _ ≪≫
    (Picard.PoincareBundle.GlobalPullbackFrame.comparison (lift t a) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] 1 h).symm) ≪≫
    Picard.PoincareBundle.GlobalPullbackFrame.comparison (lift t a) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] 1 h = _
  simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberProductOrigin.Construction
