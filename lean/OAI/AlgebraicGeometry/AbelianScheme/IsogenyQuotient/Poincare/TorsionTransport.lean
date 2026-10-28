import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.DiagonalTorsionFrame
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramePathTransport

/-! # Torsion Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionTransport.Construction

noncomputable section

/-! On n-torsion, the output half of the two-variable symmetry formula
transports the horizontal n-fold Poincare frame to the original vertical
unit frame in the common target fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {k : Type} [Field k] {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ] (n : ℕ)

theorem poincarePowerCoordinate_eq_one {T : Over (Spec (.of k))} (x : T ⟶ A.scheme) (hx : x ^ n = 1) :
    x ≫ φ ^ n = 1 :=
  ((MonObj.comp_pow φ n x).trans (MonObj.pow_comp x n φ).symm).trans
    ((congrArg (fun a => a ≫ φ) hx).trans (MonObj.one_comp φ))

def poincarePowerHorizontalFrame {T : Over (Spec (.of k))} (x y : T ⟶ A.scheme) (hx : x ^ n = 1) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (x ≫ φ ^ n) y) :=
  AxisFrames.Construction.poincareHorizontalUnitFrame D (lift (x ≫ φ ^ n) y) ((lift_fst _ _).trans (poincarePowerCoordinate_eq_one D φ n x hx))

variable
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)

def poincareTorsionOutputIso {T : Over (Spec (.of k))} (x y : T ⟶ A.scheme) (hx : x ^ n = 1) :
    Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (x ≫ φ ^ n) y) ≅
      Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (y ≫ φ) (1 : T ⟶ A.scheme)) :=
  FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (x ≫ φ ^ n) y) (lift ((x ^ n) ≫ φ) y)
      (congrArg₂ lift ((MonObj.comp_pow φ n x).trans (MonObj.pow_comp x n φ).symm) rfl) ≪≫
    SymmetryFibers.Construction.poincareSymmetryFiber D φ σ y (x ^ n) ≪≫
      FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (y ≫ φ) (x ^ n)) (lift (y ≫ φ) 1)
        (congrArg (lift (y ≫ φ)) hx)

variable
  (hd : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))

include hd in
theorem poincarePowerHorizontalFrame_output {T : Over (Spec (.of k))}
    (x y : T ⟶ A.scheme) (hx : x ^ n = 1) :
    poincarePowerHorizontalFrame D φ n x y hx ≪≫ poincareTorsionOutputIso D φ n σ x y hx =
      VerticalUnits.Construction.poincareVerticalUnitFrame D (lift (y ≫ φ) (1 : T ⟶ A.scheme)) (lift_snd _ _) := by
  have hm : lift ((x ^ n) ≫ φ) y ≫ fst D.abelian.scheme A.scheme = 1 :=
    (lift_fst _ _).trans ((congrArg (fun a => a ≫ φ) hx).trans (MonObj.one_comp φ))
  have hc := UnitFrameTargets.Construction.poincareHorizontalUnitFrame_target D (lift (x ≫ φ ^ n) y) (lift ((x ^ n) ≫ φ) y)
    ((lift_fst _ _).trans (poincarePowerCoordinate_eq_one D φ n x hx)) hm
    (congrArg₂ lift ((MonObj.comp_pow φ n x).trans (MonObj.pow_comp x n φ).symm) rfl)
  exact (FramePathTransport.Construction.frame_three_steps (poincarePowerHorizontalFrame D φ n x y hx)
    (FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) _ _
      (congrArg₂ lift ((MonObj.comp_pow φ n x).trans (MonObj.pow_comp x n φ).symm) rfl))
    (SymmetryFibers.Construction.poincareSymmetryFiber D φ σ y (x ^ n))
    (FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) _ _ (congrArg (lift (y ≫ φ)) hx))
    (AxisFrames.Construction.poincareHorizontalUnitFrame D _ hm) hc).trans
      (DiagonalTorsionFrame.Construction.poincareSymmetryFrame_zero_coordinate D φ σ hd y (x ^ n) hx hm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionTransport.Construction
