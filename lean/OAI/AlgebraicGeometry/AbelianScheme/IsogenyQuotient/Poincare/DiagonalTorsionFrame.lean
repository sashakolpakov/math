import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarSymmetryAllTests
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.SymmetryAxis
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.UnitFrameTargets
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarFrameTarget

/-! # Diagonal Torsion Frame -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.DiagonalTorsionFrame.Construction

noncomputable section

/-! The actual torsion scalar frame on a polarization diagonal is
the original vertical unit frame. The identity includes all infinitesimal
test points and uses the constructed scalar–symmetry comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ]
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)
  (hd : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))

include hd in
omit [IsAlgClosed k] in
theorem poincareSymmetryFrame_zero_coordinate {T : Over (Spec (.of k))}
    (a b : T ⟶ A.scheme) (hb : b = 1)
    (h : lift (b ≫ φ) a ≫ fst D.abelian.scheme A.scheme = 1) :
    (AxisFrames.Construction.poincareHorizontalUnitFrame D (lift (b ≫ φ) a) h ≪≫ SymmetryFibers.Construction.poincareSymmetryFiber D φ σ a b) ≪≫
      FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (a ≫ φ) b) (lift (a ≫ φ) 1)
        (congrArg (lift (a ≫ φ)) hb) =
      VerticalUnits.Construction.poincareVerticalUnitFrame D (lift (a ≫ φ) (1 : T ⟶ A.scheme)) (lift_snd _ _) := by
  cases hb
  exact (Iso.trans_refl _).trans (SymmetryAxis.Construction.poincareSymmetryAxis D φ σ hd a)

include hd in
theorem poincareTorsionScalarFrame_diagonal (n : ℕ) {T : Over (Spec (.of k))}
    (a : T ⟶ A.scheme) (ha : a ^ n = 1) (ht : (a ≫ φ) ^ n = 1) :
    ScalarFrameTarget.Construction.poincareTorsionScalarFrameTo D n (a ≫ φ) a ht (lift (a ≫ φ) 1)
      (congrArg (lift (a ≫ φ)) ha) =
      VerticalUnits.Construction.poincareVerticalUnitFrame D (lift (a ≫ φ) (1 : T ⟶ A.scheme)) (lift_snd _ _) := by
  have hm : lift ((a ^ n) ≫ φ) a ≫ fst D.abelian.scheme A.scheme = 1 :=
    (lift_fst _ _).trans ((congrArg (fun b => b ≫ φ) ha).trans (MonObj.one_comp φ))
  let s := AxisFrames.Construction.poincareHorizontalUnitFrame D (lift ((a ≫ φ) ^ n) a) ((lift_fst _ _).trans ht)
  let c := FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift ((a ≫ φ) ^ n) a) (lift ((a ^ n) ≫ φ) a)
    (congrArg₂ lift (MonObj.pow_comp a n φ).symm rfl)
  let e := SymmetryFibers.Construction.poincareSymmetryFiber D φ σ a (a ^ n)
  have hc : s ≪≫ c = AxisFrames.Construction.poincareHorizontalUnitFrame D (lift ((a ^ n) ≫ φ) a) hm :=
    UnitFrameTargets.Construction.poincareHorizontalUnitFrame_target D _ _ ((lift_fst _ _).trans ht) hm _
  have hs := congrArg (fun m => s ≪≫ m) (ScalarSymmetryAllTests.Construction.poincareScalarFiberComparison_symmetry_allTests D φ σ n hd a)
  have hf : TorsionPullbackFrame.Construction.poincareTorsionScalarFrame D n (a ≫ φ) a ht =
      AxisFrames.Construction.poincareHorizontalUnitFrame D (lift ((a ^ n) ≫ φ) a) hm ≪≫ e :=
    hs.trans ((Iso.trans_assoc s c e).symm.trans (congrArg (fun v => v ≪≫ e) hc))
  exact (congrArg (fun v => v ≪≫ FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
    (lift (a ≫ φ) (a ^ n)) (lift (a ≫ φ) 1) (congrArg (lift (a ≫ φ)) ha)) hf).trans
      (poincareSymmetryFrame_zero_coordinate D φ σ hd a (a ^ n) ha hm)

include hd in
theorem poincareTorsionScalarFrame_polarized (n : ℕ) {T : Over (Spec (.of k))}
    (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) (ht : t ^ n = 1) (ha : a ^ n = 1)
    (hta : t = a ≫ φ) :
    ScalarFrameTarget.Construction.poincareTorsionScalarFrameTo D n t a ht (lift t 1) (congrArg (lift t) ha) =
      VerticalUnits.Construction.poincareVerticalUnitFrame D (lift t (1 : T ⟶ A.scheme)) (lift_snd _ _) := by
  subst t
  exact poincareTorsionScalarFrame_diagonal D φ σ hd n a ha ht

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.DiagonalTorsionFrame.Construction
