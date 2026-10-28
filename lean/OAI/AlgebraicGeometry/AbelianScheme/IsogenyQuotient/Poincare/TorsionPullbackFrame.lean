import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarNaturality
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.AxisFrames
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberSectionIsoTransport

/-! # Torsion Pullback Frame -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionPullbackFrame.Construction

noncomputable section

section

/-! A torsion dual coordinate gives a canonical frame of the Poincare
fiber evaluated at n times the abelian coordinate. The frame is natural
on every test scheme and comes from the original axis normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (n : ℕ)

def poincareTorsionScalarFrame {T : Over (Spec (.of k))}
    (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) (ht : t ^ n = 1) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift t (a ^ n)) :=
  AxisFrames.Construction.poincareHorizontalUnitFrame D (lift (t ^ n) a) ((lift_fst _ _).trans ht) ≪≫
    ScalarLine.Construction.poincareScalarFiberComparison D n t a

theorem poincareTorsionScalarFrame_natural {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) (ht : t ^ n = 1)
    (t' : T' ⟶ D.abelian.scheme) (a' : T' ⟶ A.scheme) (ht' : t' ^ n = 1)
    (hbase : f ≫ lift t a = lift t' a')
    (hleft : f ≫ lift (t ^ n) a = lift (t' ^ n) a')
    (hright : f ≫ lift t (a ^ n) = lift t' (a' ^ n)) :
    Picard.PoincareBundle.Line.Fibers.pullSection (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f (lift t (a ^ n)) (lift t' (a' ^ n)) hright
      (poincareTorsionScalarFrame D n t a ht).hom = (poincareTorsionScalarFrame D n t' a' ht').hom := by
  exact FiberSectionIsoTransport.Construction.fiberSection_iso_transport_natural (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f _ _ _ _ hleft hright
    (ScalarLine.Construction.poincareScalarFiberComparison D n t a) (ScalarLine.Construction.poincareScalarFiberComparison D n t' a')
    (ScalarNaturality.Construction.poincareScalarFiberComparison_pullback D n f t a t' a' hbase hleft hright) _ _
    (AxisFrames.Construction.poincareHorizontalUnitFrame_natural D f _ _ ((lift_fst _ _).trans ht) ((lift_fst _ _).trans ht') hleft)

end

/-! A torsion-valued Poincare parameter canonically trivializes the
actual pullback of its family line along multiplication by n. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

def poincareTorsionFamilyLine {Q : Over (Spec (.of k))} (t : Q ⟶ D.abelian.scheme) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Q ⊗ A.scheme).left := ProductIsomorphisms.Construction.poincarePointLine D (fst Q A.scheme ≫ t) (snd Q A.scheme)

def poincareFamilyMultiplication (Q : Over (Spec (.of k))) (n : ℕ) : Q ⊗ A.scheme ⟶ Q ⊗ A.scheme :=
  𝟙 Q ⊗ₘ ((𝟙 A.scheme) ^ n)

omit [IsAlgClosed k] in
theorem poincareFamilyMultiplication_point {Q : Over (Spec (.of k))} (t : Q ⟶ D.abelian.scheme) (n : ℕ) :
    poincareFamilyMultiplication (A := A) Q n ≫ lift (fst Q A.scheme ≫ t) (snd Q A.scheme) =
      lift (fst Q A.scheme ≫ t) ((snd Q A.scheme) ^ n) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [poincareFamilyMultiplication, MonObj.comp_pow]

def poincareTorsionFamilyPullbackFrame {Q : Over (Spec (.of k))}
    (t : Q ⟶ D.abelian.scheme) (n : ℕ) (ht : t ^ n = 1) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Q ⊗ A.scheme).left ≅
      ((poincareTorsionFamilyLine D t).pullback (poincareFamilyMultiplication (A := A) Q n).left).sheaf := by
  have htn : (fst Q A.scheme ≫ t) ^ n = 1 := by
    rw [← MonObj.comp_pow, ht, MonObj.comp_one]
  exact poincareTorsionScalarFrame D n (fst Q A.scheme ≫ t) (snd Q A.scheme) htn ≪≫
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (poincareFamilyMultiplication (A := A) Q n)
      (lift (fst Q A.scheme ≫ t) (snd Q A.scheme)) (lift (fst Q A.scheme ≫ t) ((snd Q A.scheme) ^ n))
      (poincareFamilyMultiplication_point D t n)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionPullbackFrame.Construction
