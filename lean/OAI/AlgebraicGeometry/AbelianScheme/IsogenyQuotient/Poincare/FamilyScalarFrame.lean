import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PointFrameSection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberPointEquality
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionPullbackFrame

/-! # Family Scalar Frame -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.FamilyScalarFrame.Construction

noncomputable section

/-! The global torsion Poincare scalar frame recovers its explicit
fiber frame on every parameter and every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {Q : Over (Spec (.of k))} (t : Q ⟶ D.abelian.scheme) (n : ℕ) (ht : t ^ n = 1)

def poincareFamilyScalarPoint : Q ⊗ A.scheme ⟶ D.abelian.scheme ⊗ A.scheme :=
  lift (fst Q A.scheme ≫ t) ((snd Q A.scheme) ^ n)

include ht in
omit [IsAlgClosed k] in
theorem poincareFamilyDualCoordinate_pow {R : Over (Spec (.of k))} (x : R ⟶ Q ⊗ A.scheme) :
    (x ≫ fst Q A.scheme ≫ t) ^ n = 1 := by
  rw [← Category.assoc, ← MonObj.comp_pow, ht, MonObj.comp_one]

def poincareFamilyScalarFrame :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Q ⊗ A.scheme).left ≅ Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (poincareFamilyScalarPoint D t n) :=
  TorsionPullbackFrame.Construction.poincareTorsionScalarFrame D n (fst Q A.scheme ≫ t) (snd Q A.scheme)
    ((MonObj.comp_pow t n (fst Q A.scheme)).symm.trans
      ((congrArg (fun a => fst Q A.scheme ≫ a) ht).trans (MonObj.comp_one _)))

omit [IsAlgClosed k] in
theorem poincareFamilyScalarPoint_comp {R : Over (Spec (.of k))} (x : R ⟶ Q ⊗ A.scheme) :
    x ≫ poincareFamilyScalarPoint D t n = lift (x ≫ fst Q A.scheme ≫ t) ((x ≫ snd Q A.scheme) ^ n) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp only [poincareFamilyScalarPoint, Category.assoc,
    lift_fst, lift_snd, MonObj.comp_pow]

theorem poincareFamilyScalarFrame_atPoint {R : Over (Spec (.of k))} (x : R ⟶ Q ⊗ A.scheme) :
    Picard.PoincareBundle.GlobalPullbackFrame.atPoint (poincareFamilyScalarPoint D t n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (poincareFamilyScalarFrame D t n ht)
      x (lift (x ≫ fst Q A.scheme ≫ t) ((x ≫ snd Q A.scheme) ^ n)) (poincareFamilyScalarPoint_comp D t n x) =
    TorsionPullbackFrame.Construction.poincareTorsionScalarFrame D n (x ≫ fst Q A.scheme ≫ t) (x ≫ snd Q A.scheme)
      (poincareFamilyDualCoordinate_pow D t n ht x) := by
  apply PointFrameSection.Construction.atPoint_eq_of_pulled_section
  exact TorsionPullbackFrame.Construction.poincareTorsionScalarFrame_natural D n x (fst Q A.scheme ≫ t) (snd Q A.scheme) _
    (x ≫ fst Q A.scheme ≫ t) (x ≫ snd Q A.scheme) (poincareFamilyDualCoordinate_pow D t n ht x)
    (by apply CartesianMonoidalCategory.hom_ext <;> simp only [Category.assoc, lift_fst, lift_snd])
    (by apply CartesianMonoidalCategory.hom_ext <;> simp only [Category.assoc, lift_fst, lift_snd, MonObj.comp_pow])
    (poincareFamilyScalarPoint_comp D t n x)

theorem poincareFamilyScalarFrame_atPoint_to {R : Over (Spec (.of k))}
    (x : R ⟶ Q ⊗ A.scheme) (q : R ⟶ D.abelian.scheme ⊗ A.scheme)
    (hx : x ≫ poincareFamilyScalarPoint D t n = q) :
    Picard.PoincareBundle.GlobalPullbackFrame.atPoint (poincareFamilyScalarPoint D t n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
      (poincareFamilyScalarFrame D t n ht) x q hx =
    TorsionPullbackFrame.Construction.poincareTorsionScalarFrame D n (x ≫ fst Q A.scheme ≫ t) (x ≫ snd Q A.scheme)
      (poincareFamilyDualCoordinate_pow D t n ht x) ≪≫
        FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
          (lift (x ≫ fst Q A.scheme ≫ t) ((x ≫ snd Q A.scheme) ^ n)) q
          ((poincareFamilyScalarPoint_comp D t n x).symm.trans hx) := by
  have h := FiberPointEquality.Construction.atPoint_congr_target (poincareFamilyScalarPoint D t n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
    (poincareFamilyScalarFrame D t n ht) x _ q (poincareFamilyScalarPoint_comp D t n x) hx
    ((poincareFamilyScalarPoint_comp D t n x).symm.trans hx)
  exact h.symm.trans (congrArg (fun a => a ≪≫ FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) _ q
    ((poincareFamilyScalarPoint_comp D t n x).symm.trans hx))
      (poincareFamilyScalarFrame_atPoint D t n ht x))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.FamilyScalarFrame.Construction
