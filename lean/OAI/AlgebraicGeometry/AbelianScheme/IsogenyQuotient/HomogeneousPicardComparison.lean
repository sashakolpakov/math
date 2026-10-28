import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.SheafComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Picard

/-! # Homogeneous Picard Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HomogeneousPicardComparison.Construction

noncomputable section

/-! The PoincareBundle homogeneous Picard functor is the original HilbertConstruction functor,
with identical translations and the actual line-class isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

set_option backward.isDefEq.respectTransparency false in
theorem e45HomogeneousClass_iff (T : Over S)
    (q : (Picard.PoincareBundle.Functor.relativePicardPresheaf A.scheme).obj (.op T)) :
    Picard.PoincareBundle.Homogeneous.IsHomogeneous A.scheme T q ↔
      A.IsHomogeneousPicardClass T (LineClassComparison.Construction.e45LineClassEquiv _ q) := by
  constructor
  · intro h U f a
    have he := (Picard.SheafComparison.Construction.e45RelativePicardSection_eq_iff A.scheme U _ _).mp (h U f a)
    change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (LineClassComparison.Construction.e45LineClassEquiv _ (Picard.PoincareBundle.Line.Bundles.LineBundleClass.pullback (A.translation a).left
        ((Picard.PoincareBundle.Functor.relativePicardPresheaf A.scheme).map f.op q))) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
        (LineClassComparison.Construction.e45LineClassEquiv _ ((Picard.PoincareBundle.Functor.relativePicardPresheaf A.scheme).map f.op q)) at he
    rw [LineClassComparison.Construction.e45LineClassEquiv_pullback] at he
    erw [Picard.SheafComparison.Construction.e45RelativePicardPresheafIso_natural A.scheme f q] at he
    exact he
  · intro h U f a
    apply (Picard.SheafComparison.Construction.e45RelativePicardSection_eq_iff A.scheme U _ _).mpr
    change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (LineClassComparison.Construction.e45LineClassEquiv _ (Picard.PoincareBundle.Line.Bundles.LineBundleClass.pullback (A.translation a).left
        ((Picard.PoincareBundle.Functor.relativePicardPresheaf A.scheme).map f.op q))) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
        (LineClassComparison.Construction.e45LineClassEquiv _ ((Picard.PoincareBundle.Functor.relativePicardPresheaf A.scheme).map f.op q))
    rw [LineClassComparison.Construction.e45LineClassEquiv_pullback]
    erw [Picard.SheafComparison.Construction.e45RelativePicardPresheafIso_natural A.scheme f q]
    exact h U f a

set_option backward.isDefEq.respectTransparency false in
def e45HomogeneousClassEquiv (T : Over S) :
    (Picard.PoincareBundle.Homogeneous.homogeneousPresheaf A.scheme).obj (.op T) ≃
      A.homogeneousPicardPresheaf.obj (.op T) where
  toFun q := ⟨LineClassComparison.Construction.e45LineClassEquiv _ q.val, (e45HomogeneousClass_iff A T q.val).mp q.property⟩
  invFun q := ⟨(LineClassComparison.Construction.e45LineClassEquiv _).symm q.val, (e45HomogeneousClass_iff A T _).mpr (by
    change A.IsHomogeneousPicardClass T ((LineClassComparison.Construction.e45LineClassEquiv (T ⊗ A.scheme).left)
      ((LineClassComparison.Construction.e45LineClassEquiv (T ⊗ A.scheme).left).symm q.val))
    rw [Equiv.apply_symm_apply]
    exact q.property)⟩
  left_inv q := Subtype.ext ((LineClassComparison.Construction.e45LineClassEquiv _).symm_apply_apply q.val)
  right_inv q := Subtype.ext ((LineClassComparison.Construction.e45LineClassEquiv _).apply_symm_apply q.val)

def e45HomogeneousPicardPresheafIso :
    Picard.PoincareBundle.Homogeneous.homogeneousPresheaf A.scheme ≅ A.homogeneousPicardPresheaf :=
  NatIso.ofComponents (fun T => (e45HomogeneousClassEquiv A T.unop).toIso) (by
    intro T U f
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact Picard.SheafComparison.Construction.e45RelativePicardPresheafIso_natural A.scheme f.unop q.val)

def e45HomogeneousPicardSheafIso :
    Picard.PoincareBundle.Homogeneous.homogeneousSheaf A.scheme ≅ A.homogeneousPicardSheaf :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).mapIso (e45HomogeneousPicardPresheafIso A)

theorem e45HomogeneousPicardSheafIso_toSheaf (T : Over S)
    (q : (Picard.PoincareBundle.Homogeneous.homogeneousPresheaf A.scheme).obj (.op T)) :
    (e45HomogeneousPicardSheafIso A).hom.hom.app (.op T)
      ((toSheafify (Scheme.fppfTopology.over S) (Picard.PoincareBundle.Homogeneous.homogeneousPresheaf A.scheme)).app (.op T) q) =
    (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op T)
      (e45HomogeneousClassEquiv A T q) := by
  exact (congrArg (fun f => f.app (.op T) q)
    (toSheafify_naturality (Scheme.fppfTopology.over S) (e45HomogeneousPicardPresheafIso A).hom)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HomogeneousPicardComparison.Construction
