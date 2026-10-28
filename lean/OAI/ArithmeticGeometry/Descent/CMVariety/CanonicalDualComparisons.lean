import OAI.ArithmeticGeometry.Descent.CMVariety.UnpolarizedComparisons
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareDescent
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Dual
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Canonical Dual Comparisons -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.CanonicalDualComparisons.Abelian

noncomputable section

/-!
Canonical duality supplies the Poincare comparison for every actual group
isomorphism. The Poincare calculation follows the shared NeighborCounting proof,
using only its global descent theorem and avoiding unrelated isogeny
finiteness dependencies.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareDescent OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Dual

theorem canonical_dualIso_poincare {a b : ℕ}
    {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (DA : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison.dualIso DA DB e).inv ⊗ₘ e.hom).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare := by
  let d := AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison.dualIso DA DB e
  have h := congrArg (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.inv ▷ A.scheme).left)
    (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareDescent.poincareClass_eq DA DB e.hom)
  have h₁ : (d.inv ▷ A.scheme).left ≫ (DB.abelian.scheme ◁ e.hom).left =
      (d.inv ⊗ₘ e.hom).left := by
    rw [← Over.comp_left, ← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  have h₂ : (d.inv ▷ A.scheme).left ≫ (d.hom ▷ A.scheme).left =
      𝟙 (DA.abelian.scheme ⊗ A.scheme).left := by
    rw [← Over.comp_left, ← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom]
    simp only [d.inv_hom_id, Category.id_comp, tensorHom_id, id_whiskerRight]
    rfl
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.inv ▷ A.scheme).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DB.abelian.scheme ◁ e.hom).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)) =
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.inv ▷ A.scheme).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.hom ▷ A.scheme).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare)) at h
  rw [← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, h₁, h₂,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] at h
  exact h

def unpolarizedEnhancedIsoOfGroupLevel {g N r : ℕ} {δ : Fin g → ℕ}
    {A B : ModuliObjects.Abelian.EnhancedAbelianData g δ N r AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (e : A.polarized.abelian.scheme ≅ B.polarized.abelian.scheme) [IsMonHom e.hom]
    (hequiv : ∀ i, A.endomorphism i ≫ e.hom = e.hom ≫ B.endomorphism i)
    (hlevel : ∀ (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
      (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
      (A.polarized.level.hom.app (.op T) c).val ≫ e.hom =
        (B.polarized.level.hom.app (.op T) c).val) : UnpolarizedComparisons.Abelian.UnpolarizedEnhancedIso A B where
  abelian := e
  dual := (AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison.dualIso A.polarized.dual B.polarized.dual e).symm
  abelianGroup := inferInstance
  dualGroup := AlgebraicGeometry.Isogenies.NeighborCounting.Dual.dualMap_isMonHom B.polarized.dual A.polarized.dual e.inv
  poincare := canonical_dualIso_poincare A.polarized.dual B.polarized.dual e
  level := hlevel
  equivariant := hequiv

end

end OAI.ArithmeticGeometry.Descent.CMVariety.CanonicalDualComparisons.Abelian
