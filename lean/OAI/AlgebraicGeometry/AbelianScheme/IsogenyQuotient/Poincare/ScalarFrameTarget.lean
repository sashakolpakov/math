import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.FamilyScalarFrame

/-! # Scalar Frame Target -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarFrameTarget.Construction

noncomputable section

/-! Explicit Poincare torsion scalar frames transported to a prescribed
fiber; equality of their actual coordinates preserves the frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (n : ℕ)
  {T : Over (Spec (.of k))}

def poincareTorsionScalarFrameTo (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) (ht : t ^ n = 1)
    (q : T ⟶ D.abelian.scheme ⊗ A.scheme) (h : lift t (a ^ n) = q) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) q :=
  TorsionPullbackFrame.Construction.poincareTorsionScalarFrame D n t a ht ≪≫ FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) _ q h

theorem poincareTorsionScalarFrameTo_congr
    (t t' : T ⟶ D.abelian.scheme) (a a' : T ⟶ A.scheme) (ht : t ^ n = 1) (ht' : t' ^ n = 1)
    (q : T ⟶ D.abelian.scheme ⊗ A.scheme) (h : lift t (a ^ n) = q) (h' : lift t' (a' ^ n) = q)
    (et : t = t') (ea : a = a') :
    poincareTorsionScalarFrameTo D n t a ht q h = poincareTorsionScalarFrameTo D n t' a' ht' q h' := by
  cases et
  cases ea
  rfl

theorem poincareTorsionScalarFrameTo_refl (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) (ht : t ^ n = 1) :
    poincareTorsionScalarFrameTo D n t a ht (lift t (a ^ n)) rfl = TorsionPullbackFrame.Construction.poincareTorsionScalarFrame D n t a ht :=
  Iso.trans_refl _

theorem poincareFamilyScalarFrame_atPoint_explicit {Q : Over (Spec (.of k))}
    (t : Q ⟶ D.abelian.scheme) (ht : t ^ n = 1) (x : T ⟶ Q ⊗ A.scheme)
    (q : T ⟶ D.abelian.scheme ⊗ A.scheme) (hx : x ≫ FamilyScalarFrame.Construction.poincareFamilyScalarPoint D t n = q) :
    Picard.PoincareBundle.GlobalPullbackFrame.atPoint (FamilyScalarFrame.Construction.poincareFamilyScalarPoint D t n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
      (FamilyScalarFrame.Construction.poincareFamilyScalarFrame D t n ht) x q hx =
    poincareTorsionScalarFrameTo D n (x ≫ fst Q A.scheme ≫ t) (x ≫ snd Q A.scheme)
      (FamilyScalarFrame.Construction.poincareFamilyDualCoordinate_pow D t n ht x) q
      ((FamilyScalarFrame.Construction.poincareFamilyScalarPoint_comp D t n x).symm.trans hx) :=
  FamilyScalarFrame.Construction.poincareFamilyScalarFrame_atPoint_to D t n ht x q hx

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarFrameTarget.Construction
