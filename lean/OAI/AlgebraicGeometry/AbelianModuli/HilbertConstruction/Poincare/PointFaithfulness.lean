import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PicardInclusionFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.PoincareClasses

/-! # Point Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual Poincare line-bundle classes determine dual-valued points over every base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}

theorem Dual.Data.DualAbelianData.poincareAt_class_injective (D : Dual.Data.DualAbelianData A) (T : Over S) :
    Function.Injective (fun f : T ⟶ D.abelian.scheme => Line.Bundles.LineBundle.classOf (D.poincareAt f)) := by
  intro f h e
  apply D.representable.homEquiv.injective
  apply A.homogeneousPicardSectionInclusion_injective T
  exact (D.pointRelativeClass_eq_poincare f).trans
    ((congrArg ((Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)) e).trans
      (D.pointRelativeClass_eq_poincare h).symm)

theorem Dual.Data.DualAbelianData.hom_eq_of_poincarePullbackClass (D : Dual.Data.DualAbelianData A) {T : Over S}
    (f h : T ⟶ D.abelian.scheme)
    (e : Line.Bundles.LineBundle.pullbackClass (f ⊗ₘ 𝟙 A.scheme).left (Line.Bundles.LineBundle.classOf D.poincare) =
      Line.Bundles.LineBundle.pullbackClass (h ⊗ₘ 𝟙 A.scheme).left (Line.Bundles.LineBundle.classOf D.poincare)) : f = h := by
  rw [tensorHom_id, tensorHom_id] at e
  exact D.poincareAt_class_injective T e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
