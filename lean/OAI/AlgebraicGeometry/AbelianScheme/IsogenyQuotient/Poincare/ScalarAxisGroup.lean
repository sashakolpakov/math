import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.AxisFrameOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarOrigin

/-! # Scalar Axis Group -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarAxisGroup.Construction

noncomputable section

/-! The normalized scalar comparison preserves the vertical Poincare
axis frame on every proper smooth connected group parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))} [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
  (t : T ⟶ D.abelian.scheme) [IsMonHom t] (n : ℕ)

set_option backward.isDefEq.respectTransparency false in
theorem poincareScalarVerticalAxis_group :
    VerticalUnits.Construction.poincareVerticalUnitFrame D (lift (t ^ n) (1 : T ⟶ A.scheme)) (lift_snd _ _) ≪≫
      ScalarLine.Construction.poincareScalarFiberComparison D n t 1 =
    VerticalUnits.Construction.poincareVerticalUnitFrame D (lift t ((1 : T ⟶ A.scheme) ^ n))
      ((lift_snd _ _).trans (one_pow n)) := by
  have : IsMonHom (1 : T ⟶ A.scheme) := by
    rw [Hom.one_def]
    infer_instance
  have : IsIso η[T].left.appTop := ProductIsomorphisms.Construction.origin_appTop_isIso T
  apply Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.iso_unique η[T].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial T.left)
    (ProductIsomorphisms.Construction.poincarePointLine D t ((1 : T ⟶ A.scheme) ^ n))
  rw [Functor.mapIso_trans, AxisFrameOrigin.Construction.poincareVerticalUnitFrame_point_origin,
    ScalarOrigin.Construction.poincareScalarFiberComparison_origin, AxisFrameOrigin.Construction.poincareVerticalUnitFrame_point_origin]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarAxisGroup.Construction
