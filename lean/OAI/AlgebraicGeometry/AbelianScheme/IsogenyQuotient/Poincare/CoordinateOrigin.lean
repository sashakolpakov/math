import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.SymmetryFrameFormula
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormalizedProductOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberPointEquality
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsoFrameComparison

/-! # Coordinate Origin -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.CoordinateOrigin.Construction

noncomputable section

section

/-! Diagonal normalization of the original polarization family symmetry
gives the same zero-frame normalization as the Poincare scalar comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {k : Type} [Field k] {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {T : Over (Spec (.of k))} [GrpObj T]

theorem poincarePointOriginFrame_comparison_to
    (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) [IsMonHom t] [IsMonHom a]
    (q : 𝟙_ (Over (Spec (.of k))) ⟶ D.abelian.scheme ⊗ A.scheme) (hq : q = 1)
    (hx : η[T] ≫ lift t a = q) :
    OriginFrames.Construction.poincarePointOriginFrame D t a ≪≫ Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] (lift t a) q hx =
      OriginFrames.Construction.poincareZeroFrame D _ ≪≫ FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) 1 q hq.symm := by
  cases hq
  exact (FiberProductOrigin.Construction.poincarePointOriginFrame_comparison D t a hx).trans (Iso.trans_refl _).symm

variable (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ]
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)
  (hd : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))

include hd in
theorem poincareSymmetryFiber_origin (x y : T ⟶ A.scheme) [IsMonHom x] [IsMonHom y] :
    (Scheme.Modules.pullback η[T].left).mapIso (SymmetryFibers.Construction.poincareSymmetryFiber D φ σ x y) =
      (OriginFrames.Construction.poincarePointOriginFrame D (y ≫ φ) x).symm ≪≫ OriginFrames.Construction.poincarePointOriginFrame D (x ≫ φ) y := by
  let z : 𝟙_ (Over (Spec (.of k))) ⟶ D.abelian.scheme ⊗ A.scheme :=
    lift ((1 : 𝟙_ (Over (Spec (.of k))) ⟶ A.scheme) ≫ φ) 1
  have hz : z = 1 := by
    apply CartesianMonoidalCategory.hom_ext <;> simp only [z, lift_fst, lift_snd, MonObj.one_comp]
  have hl : η[T] ≫ lift (y ≫ φ) x = z := (NormalizedProductOrigin.Construction.groupMap_origin (lift (y ≫ φ) x)).trans hz.symm
  have hr : η[T] ≫ lift (x ≫ φ) y = z := (NormalizedProductOrigin.Construction.groupMap_origin (lift (x ≫ φ) y)).trans hz.symm
  have hn := SymmetryFibers.Construction.poincareSymmetryFiber_pullback D φ σ η[T] x y 1 1 (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin y) hl hr
  have h0 := SymmetryFrameFormula.Construction.poincareSymmetryFiber_diagonal D φ σ hd (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A.scheme)
  have he := hn.trans ((congrArg (fun m =>
    Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] (lift (y ≫ φ) x) z hl ≪≫ m) h0).trans
      (Iso.trans_refl _))
  exact IsoFrameComparison.Construction.iso_of_frame_square (OriginFrames.Construction.poincarePointOriginFrame D (y ≫ φ) x) (OriginFrames.Construction.poincarePointOriginFrame D (x ≫ φ) y)
    _ _ _ he ((poincarePointOriginFrame_comparison_to D (y ≫ φ) x z hz hl).trans
      (poincarePointOriginFrame_comparison_to D (x ≫ φ) y z hz hr).symm)

end

/-! Equality of actual Poincare coordinates preserves their normalized
origin frames through the canonical equality of pullback fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {k : Type} [Field k] {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {T : Over (Spec (.of k))} [GrpObj T]

theorem poincareCoordinateTransport_origin
    (t t' : T ⟶ D.abelian.scheme) (a a' : T ⟶ A.scheme)
    [IsMonHom t] [IsMonHom t'] [IsMonHom a] [IsMonHom a'] (ht : t = t') (ha : a = a') :
    (Scheme.Modules.pullback η[T].left).mapIso
      (FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift t a) (lift t' a') (congrArg₂ lift ht ha)) =
    (OriginFrames.Construction.poincarePointOriginFrame D t a).symm ≪≫ OriginFrames.Construction.poincarePointOriginFrame D t' a' := by
  cases ht
  cases ha
  rw [FiberPointEquality.Construction.fiberPointIso_refl, Functor.mapIso_refl, Iso.symm_self_id]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.CoordinateOrigin.Construction
