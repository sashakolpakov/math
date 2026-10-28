import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.CoordinateOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarOrigin

/-! # Scalar Diagonal Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarDiagonalSymmetry.Construction

noncomputable section

/-! On a proper group parameter, the scalar comparison along a
polarization diagonal is the original normalized family symmetry at
the point and its n-fold multiple. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ]
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)
  (n : ℕ)

def poincareSymmetryScalarComparison {T : Over (Spec (.of k))} (a : T ⟶ A.scheme) :
    Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift ((a ≫ φ) ^ n) a) ≅
      Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift (a ≫ φ) (a ^ n)) :=
  FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift ((a ≫ φ) ^ n) a) (lift ((a ^ n) ≫ φ) a)
    (congrArg₂ lift (MonObj.pow_comp a n φ).symm rfl) ≪≫ SymmetryFibers.Construction.poincareSymmetryFiber D φ σ a (a ^ n)

variable (hd : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))
  {T : Over (Spec (.of k))} [GrpObj T] (a : T ⟶ A.scheme) [IsMonHom a]

include hd in
omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
theorem poincareSymmetryScalarComparison_origin :
    (Scheme.Modules.pullback η[T].left).mapIso (poincareSymmetryScalarComparison D φ σ n a) =
      (OriginFrames.Construction.poincarePointOriginFrame D ((a ≫ φ) ^ n) a).symm ≪≫
        OriginFrames.Construction.poincarePointOriginFrame D (a ≫ φ) (a ^ n) := by
  unfold poincareSymmetryScalarComparison
  rw [Functor.mapIso_trans,
    CoordinateOrigin.Construction.poincareCoordinateTransport_origin D ((a ≫ φ) ^ n) ((a ^ n) ≫ φ) a a (MonObj.pow_comp a n φ).symm rfl,
    CoordinateOrigin.Construction.poincareSymmetryFiber_origin D φ σ hd]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

variable [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
  [CompactSpace T.left] [QuasiSeparatedSpace T.left]

include hd in
theorem poincareScalarFiberComparison_diagonalSymmetry :
    ScalarLine.Construction.poincareScalarFiberComparison D n (a ≫ φ) a = poincareSymmetryScalarComparison D φ σ n a := by
  have he := (Classical.choose_spec (ScalarLine.Construction.existsUnique_normalizedPoincareScalarComparison D (a ≫ φ) a n)).2
    (poincareSymmetryScalarComparison D φ σ n a) (poincareSymmetryScalarComparison_origin D φ σ n hd a)
  exact (ScalarOrigin.Construction.poincareScalarFiberComparison_eq_normalized D (a ≫ φ) a n).trans he.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarDiagonalSymmetry.Construction
