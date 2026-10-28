import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.ZeroNormalizedBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Classes

/-! # Polarization Graph Power -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every power of the canonical Poincare graph bundle is already
normalized at zero, over an arbitrary base scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (d : ℕ)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundlePower_zero_class :
    Line.Bundles.LineBundle.pullbackClass η[A.abelian.scheme].left
      (Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower d)) = 1 := by
  have hz : (Line.Bundles.LineBundle.pullbackClassMonoidHom η[A.abelian.scheme].left)
      (Line.Bundles.LineBundle.classOf A.graphBundle) = 1 := Quotient.sound ⟨A.graphBundle_zeroIso⟩
  rw [Line.Bundles.LineBundle.classOf_tensorPower]
  change (Line.Bundles.LineBundle.pullbackClassMonoidHom η[A.abelian.scheme].left) (Line.Bundles.LineBundle.classOf A.graphBundle ^ d) = 1
  rw [map_pow, hz, one_pow]

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundlePower_normalized_class :
    Line.Bundles.LineBundle.sectionNormalizeClass A.abelian.scheme.hom η[A.abelian.scheme].left
      (Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower d)) = Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower d) :=
  Line.Bundles.LineBundle.sectionNormalizeClass_fixed A.abelian.scheme.hom η[A.abelian.scheme].left
    (Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower d)) (A.graphBundlePower_zero_class d)

def PolarizationData.PolarizedAbelianWithFullLevel.graphBundlePower_normalizedIso :
    (A.abelian.zeroNormalizedBundle (A.graphBundle.tensorPower d)).sheaf ≅
      (A.graphBundle.tensorPower d).sheaf :=
  Classical.choice (Quotient.exact
    ((Line.Bundles.LineBundle.classOf_sectionNormalized A.abelian.scheme.hom η[A.abelian.scheme].left _).trans
      (A.graphBundlePower_normalized_class d)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
