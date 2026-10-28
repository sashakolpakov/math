import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberProductOrigin

/-! # Normalized Product Origin -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormalizedProductOrigin.Construction

noncomputable section

/-! The original normalized Poincare products become multiplication
in the common zero frame after the canonical fiber comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

universe u

theorem groupMap_origin {S : Scheme.{u}} {T E : Over S} [GrpObj T] [GrpObj E]
    (f : T ⟶ E) [IsMonHom f] : η[T] ≫ f = 1 := by
  rw [MonObj.one_eq_one]
  exact MonObj.one_comp f

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))} [GrpObj T] [CompactSpace T.left] [QuasiSeparatedSpace T.left]
  [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]

attribute [local instance] Poincare.OriginFrames.Construction.poincareGroupMapMul_isMonHom

theorem normalizedPoincareBilinearLeft_at_origin
    (t v : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) [IsMonHom t] [IsMonHom v] [IsMonHom a] :
    Picard.PoincareBundle.Line.Fibers.pullBilinear (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] (lift t a) (lift v a) (lift (t * v) a) 1 1 1
      (groupMap_origin (lift t a)) (groupMap_origin (lift v a)) (groupMap_origin (lift (t * v) a))
      (Poincare.BilinearProducts.Construction.normalizedPoincareBilinearLeft D t v a) =
        Poincare.BilinearProducts.Construction.framedLineProduct (Poincare.OriginFrames.Construction.poincareZeroFrame D _) (Poincare.OriginFrames.Construction.poincareZeroFrame D _) (Poincare.OriginFrames.Construction.poincareZeroFrame D _) := by
  exact FiberProductOrigin.Construction.pullBilinear_of_framed_pullback (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T]
    (lift t a) (lift v a) (lift (t * v) a) 1 1 1
    (groupMap_origin (lift t a)) (groupMap_origin (lift v a)) (groupMap_origin (lift (t * v) a))
    (Poincare.BilinearProducts.Construction.normalizedPoincareBilinearLeft D t v a)
    (Poincare.OriginFrames.Construction.poincarePointOriginFrame D t a) (Poincare.OriginFrames.Construction.poincarePointOriginFrame D v a) (Poincare.OriginFrames.Construction.poincarePointOriginFrame D (t * v) a)
    (Poincare.OriginFrames.Construction.poincareZeroFrame D _) (Poincare.OriginFrames.Construction.poincareZeroFrame D _) (Poincare.OriginFrames.Construction.poincareZeroFrame D _)
    (FiberProductOrigin.Construction.poincarePointOriginFrame_comparison D t a _) (FiberProductOrigin.Construction.poincarePointOriginFrame_comparison D v a _)
    (FiberProductOrigin.Construction.poincarePointOriginFrame_comparison D (t * v) a _) (Poincare.BilinearProducts.Construction.normalizedPoincareBilinearLeft_origin D t v a)

theorem normalizedPoincareBilinearRight_at_origin
    (t : T ⟶ D.abelian.scheme) (a b : T ⟶ A.scheme) [IsMonHom t] [IsMonHom a] [IsMonHom b] :
    Picard.PoincareBundle.Line.Fibers.pullBilinear (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] (lift t a) (lift t b) (lift t (a * b)) 1 1 1
      (groupMap_origin (lift t a)) (groupMap_origin (lift t b)) (groupMap_origin (lift t (a * b)))
      (Poincare.BilinearProducts.Construction.normalizedPoincareBilinearRight D t a b) =
        Poincare.BilinearProducts.Construction.framedLineProduct (Poincare.OriginFrames.Construction.poincareZeroFrame D _) (Poincare.OriginFrames.Construction.poincareZeroFrame D _) (Poincare.OriginFrames.Construction.poincareZeroFrame D _) := by
  exact FiberProductOrigin.Construction.pullBilinear_of_framed_pullback (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T]
    (lift t a) (lift t b) (lift t (a * b)) 1 1 1
    (groupMap_origin (lift t a)) (groupMap_origin (lift t b)) (groupMap_origin (lift t (a * b)))
    (Poincare.BilinearProducts.Construction.normalizedPoincareBilinearRight D t a b)
    (Poincare.OriginFrames.Construction.poincarePointOriginFrame D t a) (Poincare.OriginFrames.Construction.poincarePointOriginFrame D t b) (Poincare.OriginFrames.Construction.poincarePointOriginFrame D t (a * b))
    (Poincare.OriginFrames.Construction.poincareZeroFrame D _) (Poincare.OriginFrames.Construction.poincareZeroFrame D _) (Poincare.OriginFrames.Construction.poincareZeroFrame D _)
    (FiberProductOrigin.Construction.poincarePointOriginFrame_comparison D t a _) (FiberProductOrigin.Construction.poincarePointOriginFrame_comparison D t b _)
    (FiberProductOrigin.Construction.poincarePointOriginFrame_comparison D t (a * b) _) (Poincare.BilinearProducts.Construction.normalizedPoincareBilinearRight_origin D t a b)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormalizedProductOrigin.Construction
