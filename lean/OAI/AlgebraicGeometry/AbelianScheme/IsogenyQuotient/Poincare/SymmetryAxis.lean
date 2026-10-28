import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.CoordinateOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.AxisFrameOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarVerticalAxis

/-! # Symmetry Axis -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.SymmetryAxis.Construction

noncomputable section

/-! The normalized polarization symmetry carries the horizontal
Poincare unit frame to the vertical unit frame on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {k : Type} [Field k] {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ]
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)
  (hd : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))

include hd in
set_option backward.isDefEq.respectTransparency false in
theorem poincareSymmetryAxis_group {T : Over (Spec (.of k))} [GrpObj T]
    [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
    (x : T ⟶ A.scheme) [IsMonHom x] :
    AxisFrames.Construction.poincareHorizontalUnitFrame D (lift ((1 : T ⟶ A.scheme) ≫ φ) x)
      ((lift_fst _ _).trans (MonObj.one_comp φ)) ≪≫ SymmetryFibers.Construction.poincareSymmetryFiber D φ σ x 1 =
      VerticalUnits.Construction.poincareVerticalUnitFrame D (lift (x ≫ φ) (1 : T ⟶ A.scheme)) (lift_snd _ _) := by
  have : IsMonHom (1 : T ⟶ A.scheme) := by rw [Hom.one_def]; infer_instance
  have : IsIso η[T].left.appTop := ProductIsomorphisms.Construction.origin_appTop_isIso T
  apply Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.iso_unique η[T].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial T.left)
    (ProductIsomorphisms.Construction.poincarePointLine D (x ≫ φ) 1)
  rw [Functor.mapIso_trans, AxisFrameOrigin.Construction.poincareHorizontalUnitFrame_point_origin,
    CoordinateOrigin.Construction.poincareSymmetryFiber_origin D φ σ hd, AxisFrameOrigin.Construction.poincareVerticalUnitFrame_point_origin]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

include hd in
theorem poincareSymmetryAxis {T : Over (Spec (.of k))} (x : T ⟶ A.scheme) :
    AxisFrames.Construction.poincareHorizontalUnitFrame D (lift ((1 : T ⟶ A.scheme) ≫ φ) x)
      ((lift_fst _ _).trans (MonObj.one_comp φ)) ≪≫ SymmetryFibers.Construction.poincareSymmetryFiber D φ σ x 1 =
      VerticalUnits.Construction.poincareVerticalUnitFrame D (lift (x ≫ φ) (1 : T ⟶ A.scheme)) (lift_snd _ _) := by
  have hl : x ≫ lift ((1 : A.scheme ⟶ A.scheme) ≫ φ) (𝟙 A.scheme) =
      lift ((1 : T ⟶ A.scheme) ≫ φ) x := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst, ← Category.assoc, MonObj.comp_one]
    · simp only [Category.assoc, lift_snd, Category.comp_id]
  have hr : x ≫ lift ((𝟙 A.scheme) ≫ φ) (1 : A.scheme ⟶ A.scheme) =
      lift (x ≫ φ) (1 : T ⟶ A.scheme) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, lift_fst, lift_snd, Category.id_comp, MonObj.comp_one]
  have hn := SymmetryFibers.Construction.poincareSymmetryFiber_pullback D φ σ x (𝟙 A.scheme) 1 x 1
    (Category.comp_id x) (MonObj.comp_one x) hl hr
  exact ScalarVerticalAxis.Construction.fiberFrame_iso_transport_eq (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x _ _ _ _ hl hr
    (SymmetryFibers.Construction.poincareSymmetryFiber D φ σ (𝟙 A.scheme) 1) (SymmetryFibers.Construction.poincareSymmetryFiber D φ σ x 1) hn
    (AxisFrames.Construction.poincareHorizontalUnitFrame D _ ((lift_fst _ _).trans (MonObj.one_comp φ)))
    (AxisFrames.Construction.poincareHorizontalUnitFrame D _ ((lift_fst _ _).trans (MonObj.one_comp φ)))
    (VerticalUnits.Construction.poincareVerticalUnitFrame D _ (lift_snd _ _)) (VerticalUnits.Construction.poincareVerticalUnitFrame D _ (lift_snd _ _))
    (AxisFrames.Construction.poincareHorizontalUnitFrame_natural D x _ _
      ((lift_fst _ _).trans (MonObj.one_comp φ)) ((lift_fst _ _).trans (MonObj.one_comp φ)) hl)
    (VerticalUnits.Construction.poincareVerticalUnitFrame_natural D x _ _ (lift_snd _ _) (lift_snd _ _) hr)
    (poincareSymmetryAxis_group D φ σ hd (𝟙 A.scheme))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.SymmetryAxis.Construction
