import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarDiagonalSymmetry

/-! # Two Variable Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TwoVariableSymmetry.Construction

noncomputable section

/-! The full two-variable scalar comparison is built from the
normalized polarization symmetry and the symmetry of its n-fold
multiple, with both power-coordinate transports explicit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ] (n : ℕ)
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)
  (σn : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n)).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n)).sheaf)

def poincareTwoVariableSymmetryComparison {T : Over (Spec (.of k))} (x y : T ⟶ A.scheme) :
    Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift ((y ≫ φ) ^ n) x) ≅
      Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (y ≫ φ) (x ^ n)) :=
  FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift ((y ≫ φ) ^ n) x) (lift (y ≫ φ ^ n) x)
      (congrArg₂ lift (MonObj.comp_pow φ n y).symm rfl) ≪≫
    SymmetryFibers.Construction.poincareSymmetryFiber D (φ ^ n) σn x y ≪≫
      FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (x ≫ φ ^ n) y) (lift ((x ^ n) ≫ φ) y)
        (congrArg₂ lift ((MonObj.comp_pow φ n x).trans (MonObj.pow_comp x n φ).symm) rfl) ≪≫
          SymmetryFibers.Construction.poincareSymmetryFiber D φ σ y (x ^ n)

variable
  (hd : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))
  (hdn : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σn =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n)) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))
  {T : Over (Spec (.of k))} [GrpObj T] (x y : T ⟶ A.scheme) [IsMonHom x] [IsMonHom y]

include hd hdn in
omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
theorem poincareTwoVariableSymmetryComparison_origin :
    (Scheme.Modules.pullback η[T].left).mapIso (poincareTwoVariableSymmetryComparison D φ n σ σn x y) =
      (OriginFrames.Construction.poincarePointOriginFrame D ((y ≫ φ) ^ n) x).symm ≪≫
        OriginFrames.Construction.poincarePointOriginFrame D (y ≫ φ) (x ^ n) := by
  unfold poincareTwoVariableSymmetryComparison
  rw [Functor.mapIso_trans, Functor.mapIso_trans, Functor.mapIso_trans,
    CoordinateOrigin.Construction.poincareCoordinateTransport_origin D ((y ≫ φ) ^ n) (y ≫ φ ^ n) x x (MonObj.comp_pow φ n y).symm rfl,
    CoordinateOrigin.Construction.poincareSymmetryFiber_origin D (φ ^ n) σn hdn,
    CoordinateOrigin.Construction.poincareCoordinateTransport_origin D (x ≫ φ ^ n) ((x ^ n) ≫ φ) y y
      ((MonObj.comp_pow φ n x).trans (MonObj.pow_comp x n φ).symm) rfl,
    CoordinateOrigin.Construction.poincareSymmetryFiber_origin D φ σ hd]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

variable [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
  [CompactSpace T.left] [QuasiSeparatedSpace T.left]

include hd hdn in
theorem poincareScalarFiberComparison_twoVariableSymmetry :
    ScalarLine.Construction.poincareScalarFiberComparison D n (y ≫ φ) x = poincareTwoVariableSymmetryComparison D φ n σ σn x y := by
  have he := (Classical.choose_spec (ScalarLine.Construction.existsUnique_normalizedPoincareScalarComparison D (y ≫ φ) x n)).2
    (poincareTwoVariableSymmetryComparison D φ n σ σn x y)
    (poincareTwoVariableSymmetryComparison_origin D φ n σ σn hd hdn x y)
  exact (ScalarOrigin.Construction.poincareScalarFiberComparison_eq_normalized D (y ≫ φ) x n).trans he.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TwoVariableSymmetry.Construction
