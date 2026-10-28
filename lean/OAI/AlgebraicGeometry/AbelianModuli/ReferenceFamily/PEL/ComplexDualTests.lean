import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualReduction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.SmoothAffineDualProduct
import Mathlib.Analysis.Complex.Basic

/-! # Complex Dual Tests -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.ComplexDualTests

noncomputable section

/-! The complex point and its actual dual-number thickening as test
schemes over the specified number field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] (κ : K →+* ℂ)

abbrev pelComplexTest : Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom κ))

abbrev pelComplexDualTest : Over (Spec (.of K)) :=
  Over.mk (Smooth.AffineDualProduct.dualBaseProjection ℂ ≫ Spec.map (CommRingCat.ofHom κ))

def pelComplexDualProjection : pelComplexDualTest κ ⟶ pelComplexTest κ :=
  Over.homMk (Smooth.AffineDualProduct.dualBaseProjection ℂ) rfl

def pelComplexDualReduction : pelComplexTest κ ⟶ pelComplexDualTest κ :=
  Over.homMk (Smooth.AffineDualProduct.dualBaseReduction ℂ) (by
    change Smooth.AffineDualProduct.dualBaseReduction ℂ ≫ (Smooth.AffineDualProduct.dualBaseProjection ℂ ≫ Spec.map (CommRingCat.ofHom κ)) = _
    rw [← Category.assoc, Normalized.SmoothAffineDualProduct.dualBaseReduction_projection, Category.id_comp]
    rfl)

theorem pelComplexDualReduction_projection :
    pelComplexDualReduction κ ≫ pelComplexDualProjection κ = 𝟙 (pelComplexTest κ) := by
  apply Over.OverMorphism.ext
  exact Normalized.SmoothAffineDualProduct.dualBaseReduction_projection ℂ

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.ComplexDualTests
