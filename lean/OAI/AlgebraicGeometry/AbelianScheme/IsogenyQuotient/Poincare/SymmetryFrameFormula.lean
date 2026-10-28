import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.SymmetryFibers
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CompositeFiberTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricFrameDiagonal

/-! # Symmetry Frame Formula -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.SymmetryFrameFormula.Construction

noncomputable section

/-! The symmetry on original Poincare fibers is the symmetry of the
actual family line with its canonical fiber comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (φ : A.scheme ⟶ D.abelian.scheme)
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)

theorem poincareSymmetryFiber_formula {T : Over S} (x y : T ⟶ A.scheme)
    (hs : lift x y ≫ (β_ A.scheme A.scheme).hom = lift y x) :
    SymmetryFibers.Construction.poincareSymmetryFiber D φ σ x y =
      (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift y x) (φ ⊗ₘ 𝟙 A.scheme)
        (lift (y ≫ φ) x) (SymmetryFibers.Construction.poincareSymmetryTarget_point D φ y x)).symm ≪≫
      (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ) (lift x y)
        (β_ A.scheme A.scheme).hom (lift y x) hs).symm ≪≫
      (Scheme.Modules.pullback (lift x y).left).mapIso σ ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift x y) (φ ⊗ₘ 𝟙 A.scheme)
        (lift (x ≫ φ) y) (SymmetryFibers.Construction.poincareSymmetryTarget_point D φ x y) :=
  CompositeFiberTransport.Construction.globalFiberIsoTransport_composite_source (β_ A.scheme A.scheme).hom (φ ⊗ₘ 𝟙 A.scheme)
    (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) σ (lift x y) (lift y x) _ _ hs
    (SymmetryFibers.Construction.poincareSymmetryTarget_point D φ y x) (SymmetryFibers.Construction.poincareSymmetryTarget_point D φ x y)
    (SymmetryFibers.Construction.poincareSymmetrySource_point D φ x y)

set_option backward.isDefEq.respectTransparency false in
theorem poincareSymmetryFiber_diagonal
    (hd : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
      Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
        (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
        (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))
    {T : Over S} (x : T ⟶ A.scheme) :
    SymmetryFibers.Construction.poincareSymmetryFiber D φ σ x x = Iso.refl (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (x ≫ φ) x)) := by
  have hc : lift x x ≫ (β_ A.scheme A.scheme).hom = lift x x := by
    apply CartesianMonoidalCategory.hom_ext <;> simp only [Category.assoc, braiding_hom_fst,
      braiding_hom_snd, lift_fst, lift_snd]
  have hx : x ≫ DiagonalLineSymmetry.Construction.groupDiagonal A.scheme = lift x x := by
    apply CartesianMonoidalCategory.hom_ext <;> simp only [DiagonalLineSymmetry.Construction.groupDiagonal, Category.assoc, lift_fst,
      lift_snd, Category.comp_id]
  have hs := SymmetricFrameDiagonal.Construction.fixedLineSymmetry_at_point (β_ A.scheme A.scheme).hom (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
    (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme) (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ) σ hd x (lift x x) hx hc
  have he : (Scheme.Modules.pullback (lift x x).left).mapIso σ =
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ) (lift x x)
        (β_ A.scheme A.scheme).hom (lift x x) hc :=
    hs.trans (FiberProductOrigin.Construction.fiberPullbackIso_eq_comparison _ _ _ _ _).symm
  rw [poincareSymmetryFiber_formula D φ σ x x hc, he]
  simp only [Iso.symm_self_id_assoc, Iso.symm_self_id]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.SymmetryFrameFormula.Construction
