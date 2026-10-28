import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TwoVariableAllTests
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionTransport

/-! # Torsion Symmetry Ratio -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionSymmetryRatio.Construction

noncomputable section

/-! The torsion scalar-frame ratio equals the two-variable symmetry
ratio in the n-fold Poincare fiber. Both frames pass through the same
explicit output isomorphism, so their ratio is unchanged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ] (n : ℕ)
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)
  (σn : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n)).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n)).sheaf)
  (hd : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))
  (hdn : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σn =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n)) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))

include hd hdn in
theorem poincareTorsionScalarFrame_second_output {T : Over (Spec (.of k))}
    (x y : T ⟶ A.scheme) (hx : x ^ n = 1) (hy : y ^ n = 1) (ht : (y ≫ φ) ^ n = 1) :
    ScalarFrameTarget.Construction.poincareTorsionScalarFrameTo D n (y ≫ φ) x ht (lift (y ≫ φ) 1) (congrArg (lift (y ≫ φ)) hx) =
      (TorsionTransport.Construction.poincarePowerHorizontalFrame D φ n y x hy ≪≫ SymmetryFibers.Construction.poincareSymmetryFiber D (φ ^ n) σn x y) ≪≫
        TorsionTransport.Construction.poincareTorsionOutputIso D φ n σ x y hx := by
  let s := AxisFrames.Construction.poincareHorizontalUnitFrame D (lift ((y ≫ φ) ^ n) x) ((lift_fst _ _).trans ht)
  let a := FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift ((y ≫ φ) ^ n) x) (lift (y ≫ φ ^ n) x)
    (congrArg₂ lift (MonObj.comp_pow φ n y).symm rfl)
  let b := SymmetryFibers.Construction.poincareSymmetryFiber D (φ ^ n) σn x y
  let c := FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (x ≫ φ ^ n) y) (lift ((x ^ n) ≫ φ) y)
    (congrArg₂ lift ((MonObj.comp_pow φ n x).trans (MonObj.pow_comp x n φ).symm) rfl)
  let d := SymmetryFibers.Construction.poincareSymmetryFiber D φ σ y (x ^ n)
  let e := FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (y ≫ φ) (x ^ n)) (lift (y ≫ φ) 1)
    (congrArg (lift (y ≫ φ)) hx)
  have ha : s ≪≫ a = TorsionTransport.Construction.poincarePowerHorizontalFrame D φ n y x hy :=
    UnitFrameTargets.Construction.poincareHorizontalUnitFrame_target D _ _ ((lift_fst _ _).trans ht)
      ((lift_fst _ _).trans (TorsionTransport.Construction.poincarePowerCoordinate_eq_one D φ n y hy)) _
  have hs := congrArg (fun m => (s ≪≫ m) ≪≫ e)
    (TwoVariableAllTests.Construction.poincareScalarFiberComparison_twoVariable_allTests D φ n σ σn hd hdn x y)
  exact hs.trans (FramePathTransport.Construction.frame_four_steps s a b c d e (TorsionTransport.Construction.poincarePowerHorizontalFrame D φ n y x hy) ha)

include hd hdn in
theorem poincareTorsionScalarFrame_symmetryRatio {T : Over (Spec (.of k))}
    (x y : T ⟶ A.scheme) (hx : x ^ n = 1) (hy : y ^ n = 1) (ht : (y ≫ φ) ^ n = 1) :
    Picard.PoincareBundle.Line.FrameUnits.frameRatio (VerticalUnits.Construction.poincareVerticalUnitFrame D (lift (y ≫ φ) (1 : T ⟶ A.scheme)) (lift_snd _ _))
      (ScalarFrameTarget.Construction.poincareTorsionScalarFrameTo D n (y ≫ φ) x ht (lift (y ≫ φ) 1) (congrArg (lift (y ≫ φ)) hx)) =
    Picard.PoincareBundle.Line.FrameUnits.frameRatio (TorsionTransport.Construction.poincarePowerHorizontalFrame D φ n x y hx)
      (TorsionTransport.Construction.poincarePowerHorizontalFrame D φ n y x hy ≪≫ SymmetryFibers.Construction.poincareSymmetryFiber D (φ ^ n) σn x y) :=
  (congrArg₂ Picard.PoincareBundle.Line.FrameUnits.frameRatio (TorsionTransport.Construction.poincarePowerHorizontalFrame_output D φ n σ hd x y hx).symm
    (poincareTorsionScalarFrame_second_output D φ n σ σn hd hdn x y hx hy ht)).trans
      (Picard.PoincareBundle.FrameRatioPullback.frameRatio_postcomp (TorsionTransport.Construction.poincarePowerHorizontalFrame D φ n x y hx)
        (TorsionTransport.Construction.poincarePowerHorizontalFrame D φ n y x hy ≪≫ SymmetryFibers.Construction.poincareSymmetryFiber D (φ ^ n) σn x y)
        (TorsionTransport.Construction.poincareTorsionOutputIso D φ n σ x y hx))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionSymmetryRatio.Construction
