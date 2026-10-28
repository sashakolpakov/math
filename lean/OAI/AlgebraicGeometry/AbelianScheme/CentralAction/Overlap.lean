import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TensorKernelPair
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PoincareNormalization

/-! # Overlap -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Overlap.Construction

noncomputable section

/-! The overlap of an etale quotient of abelian varieties is smooth,
so the proved identity-slice scalar rigidity applies to that overlap. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

theorem over_kernelPair_isPullback_left {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B) :
    IsPullback (pullback.fst f f).left (pullback.snd f f).left f.left f.left :=
  (Over.forget S).map_isPullback (IsPullback.of_hasPullback f f)

theorem over_kernelPair_projection_etale {S : Scheme.{u}} {A B : Over S}
    (f : A ⟶ B) [Etale f.left] : Etale (pullback.fst f f).left :=
  MorphismProperty.of_isPullback (over_kernelPair_isPullback_left f).flip inferInstance

theorem abelian_quotient_overlap_zeroSlice_bijective
    {k : Type} [Field k] [IsAlgClosed k] {g h j : ℕ}
    (H : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k)))
    (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme j (Spec (.of k))) (f : A.scheme ⟶ B.scheme) [Etale f.left] :
    Function.Bijective
      (lift (1 : pullback f f ⟶ H.scheme) (𝟙 (pullback f f))).left.appTop := by
  have : ConnectedSpace H.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton H.scheme.hom
  have : IsReduced H.scheme.left :=
    Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field H.scheme.hom
  have : Etale (pullback.fst f f).left := over_kernelPair_projection_etale f
  have : Smooth (pullback f f).hom := by
    rw [← (pullback.fst f f).w]
    infer_instance
  have : Smooth (H.scheme ⊗ pullback f f).hom := by dsimp; infer_instance
  have : IsReduced (H.scheme ⊗ pullback f f).left :=
    Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field (H.scheme ⊗ pullback f f).hom
  exact ZeroSliceScalars.Construction.zeroSlice_global_function_bijective H.scheme (pullback f f) η[H.scheme]

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Overlap.Construction
