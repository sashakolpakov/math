import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarLine
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalFiberIsoTransport

/-! # Scalar Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarNaturality.Construction

noncomputable section

/-! The normalized Poincare scalar comparison retains the full
geometric pullback law on arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (n : ℕ)

theorem poincareScalarFiberComparison_eq_transport {T : Over (Spec (.of k))}
    (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    ScalarLine.Construction.poincareScalarFiberComparison D n t a = GlobalFiberIsoTransport.Construction.globalFiberIsoTransport
      (lift ((fst D.abelian.scheme A.scheme) ^ n) (snd D.abelian.scheme A.scheme))
      (lift (fst D.abelian.scheme A.scheme) ((snd D.abelian.scheme A.scheme) ^ n))
      (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (ScalarLine.Construction.poincareGlobalScalarComparison D n) (lift t a)
      (lift (t ^ n) a) (lift t (a ^ n))
      (ScalarLine.Construction.poincareScalarParameter_left D n t a) (ScalarLine.Construction.poincareScalarParameter_right D n t a) := by
  unfold ScalarLine.Construction.poincareScalarFiberComparison
  rw [FiberProductOrigin.Construction.fiberPullbackIso_eq_comparison, FiberProductOrigin.Construction.fiberPullbackIso_eq_comparison]
  rfl

theorem poincareScalarFiberComparison_pullback {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme)
    (t' : T' ⟶ D.abelian.scheme) (a' : T' ⟶ A.scheme)
    (hbase : f ≫ lift t a = lift t' a')
    (hleft : f ≫ lift (t ^ n) a = lift (t' ^ n) a')
    (hright : f ≫ lift t (a ^ n) = lift t' (a' ^ n)) :
    (Scheme.Modules.pullback f.left).mapIso (ScalarLine.Construction.poincareScalarFiberComparison D n t a) ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f (lift t (a ^ n)) (lift t' (a' ^ n)) hright =
    Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f (lift (t ^ n) a) (lift (t' ^ n) a') hleft ≪≫
      ScalarLine.Construction.poincareScalarFiberComparison D n t' a' := by
  rw [poincareScalarFiberComparison_eq_transport, poincareScalarFiberComparison_eq_transport]
  exact GlobalFiberIsoTransport.Construction.globalFiberIsoTransport_pullback _ _ (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (ScalarLine.Construction.poincareGlobalScalarComparison D n)
    f (lift t a) _ _ (ScalarLine.Construction.poincareScalarParameter_left D n t a) (ScalarLine.Construction.poincareScalarParameter_right D n t a)
    (lift t' a') _ _ (ScalarLine.Construction.poincareScalarParameter_left D n t' a') (ScalarLine.Construction.poincareScalarParameter_right D n t' a')
    hbase hleft hright

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarNaturality.Construction
