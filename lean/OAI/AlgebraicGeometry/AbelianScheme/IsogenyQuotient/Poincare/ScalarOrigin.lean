import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsoFrameComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarNaturality
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberProductOrigin

/-! # Scalar Origin -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarOrigin.Construction

noncomputable section

section

/-! The normalized scalar comparison is the identity on the original
Poincare fiber at zero, with its actual geometric pullback comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))} [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
  [CompactSpace T.left] [QuasiSeparatedSpace T.left]
  (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) [IsMonHom t] [IsMonHom a] (n : ℕ)

theorem normalizedPoincareScalarComparison_at_origin :
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] (lift (t ^ n) a) 1
      (NormalizedProductOrigin.Construction.groupMap_origin (lift (t ^ n) a))).symm ≪≫
        (Scheme.Modules.pullback η[T].left).mapIso (ScalarLine.Construction.normalizedPoincareScalarComparison D t a n) ≪≫
          Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] (lift t (a ^ n)) 1
            (NormalizedProductOrigin.Construction.groupMap_origin (lift t (a ^ n))) = Iso.refl (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (1 : 𝟙_ (Over (Spec (.of k))) ⟶ _)) := by
  have h := congrArg (fun e =>
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] (lift (t ^ n) a) 1
      (NormalizedProductOrigin.Construction.groupMap_origin (lift (t ^ n) a))).symm ≪≫ e ≪≫
        Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] (lift t (a ^ n)) 1
          (NormalizedProductOrigin.Construction.groupMap_origin (lift t (a ^ n)))) (ScalarLine.Construction.normalizedPoincareScalarComparison_origin D t a n)
  exact h.trans (IsoFrameComparison.Construction.iso_frame_comparison_identity (OriginFrames.Construction.poincarePointOriginFrame D (t ^ n) a)
    (OriginFrames.Construction.poincarePointOriginFrame D t (a ^ n)) _ _
      ((FiberProductOrigin.Construction.poincarePointOriginFrame_comparison D (t ^ n) a _).trans
        (FiberProductOrigin.Construction.poincarePointOriginFrame_comparison D t (a ^ n) _).symm))

end

section

/-! The universal scalar comparison specializes to the identity in the
common Poincare zero fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (n : ℕ)

attribute [local instance] ScalarLine.Construction.poincareScalarParameter_smooth ScalarLine.Construction.poincareScalarParameter_proper ScalarLine.Construction.poincareScalarParameter_connected

theorem poincareGlobalScalarTransport_origin :
    GlobalFiberIsoTransport.Construction.globalFiberIsoTransport
      (lift ((fst D.abelian.scheme A.scheme) ^ n) (snd D.abelian.scheme A.scheme))
      (lift (fst D.abelian.scheme A.scheme) ((snd D.abelian.scheme A.scheme) ^ n))
      (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (ScalarLine.Construction.poincareGlobalScalarComparison D n)
      η[D.abelian.scheme ⊗ A.scheme] 1 1 (NormalizedProductOrigin.Construction.groupMap_origin _) (NormalizedProductOrigin.Construction.groupMap_origin _) =
        Iso.refl (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (1 : 𝟙_ (Over (Spec (.of k))) ⟶ _)) := by
  have : CompactSpace (D.abelian.scheme ⊗ A.scheme).left :=
    QuasiCompact.compactSpace_of_compactSpace (D.abelian.scheme ⊗ A.scheme).hom
  have : QuasiSeparatedSpace (D.abelian.scheme ⊗ A.scheme).left :=
    quasiSeparatedSpace_of_quasiSeparated (D.abelian.scheme ⊗ A.scheme).hom
  have h := normalizedPoincareScalarComparison_at_origin D
    (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) n
  rw [FiberProductOrigin.Construction.fiberPullbackIso_eq_comparison, FiberProductOrigin.Construction.fiberPullbackIso_eq_comparison] at h
  exact h

end

/-! The scalar comparison over any proper group parameter retains
the original zero-frame normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))} [GrpObj T]
  (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) [IsMonHom t] [IsMonHom a] (n : ℕ)

theorem poincareScalarFiberComparison_origin :
    (Scheme.Modules.pullback η[T].left).mapIso (ScalarLine.Construction.poincareScalarFiberComparison D n t a) =
      (OriginFrames.Construction.poincarePointOriginFrame D (t ^ n) a).symm ≪≫ OriginFrames.Construction.poincarePointOriginFrame D t (a ^ n) := by
  let p := lift ((fst D.abelian.scheme A.scheme) ^ n) (snd D.abelian.scheme A.scheme)
  let q := lift (fst D.abelian.scheme A.scheme) ((snd D.abelian.scheme A.scheme) ^ n)
  have hbase : η[T] ≫ lift t a = η[D.abelian.scheme ⊗ A.scheme] :=
    (NormalizedProductOrigin.Construction.groupMap_origin (lift t a)).trans (MonObj.one_eq_one _).symm
  have h := GlobalFiberIsoTransport.Construction.globalFiberIsoTransport_pullback p q (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (ScalarLine.Construction.poincareGlobalScalarComparison D n)
    η[T] (lift t a) (lift (t ^ n) a) (lift t (a ^ n))
    (ScalarLine.Construction.poincareScalarParameter_left D n t a) (ScalarLine.Construction.poincareScalarParameter_right D n t a)
    η[D.abelian.scheme ⊗ A.scheme] 1 1 (NormalizedProductOrigin.Construction.groupMap_origin p) (NormalizedProductOrigin.Construction.groupMap_origin q) hbase
    (NormalizedProductOrigin.Construction.groupMap_origin (lift (t ^ n) a)) (NormalizedProductOrigin.Construction.groupMap_origin (lift t (a ^ n)))
  rw [poincareGlobalScalarTransport_origin, Iso.trans_refl] at h
  rw [ScalarNaturality.Construction.poincareScalarFiberComparison_eq_transport]
  exact IsoFrameComparison.Construction.iso_of_frame_square (OriginFrames.Construction.poincarePointOriginFrame D (t ^ n) a) (OriginFrames.Construction.poincarePointOriginFrame D t (a ^ n)) _ _ _ h
    ((FiberProductOrigin.Construction.poincarePointOriginFrame_comparison D (t ^ n) a _).trans
      (FiberProductOrigin.Construction.poincarePointOriginFrame_comparison D t (a ^ n) _).symm)

variable [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
  [CompactSpace T.left] [QuasiSeparatedSpace T.left]

theorem poincareScalarFiberComparison_eq_normalized :
    ScalarLine.Construction.poincareScalarFiberComparison D n t a = ScalarLine.Construction.normalizedPoincareScalarComparison D t a n :=
  (Classical.choose_spec (ScalarLine.Construction.existsUnique_normalizedPoincareScalarComparison D t a n)).2 _
    (poincareScalarFiberComparison_origin D t a n)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarOrigin.Construction
