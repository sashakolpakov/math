import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.DualProductPoincare
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductNormalizationFromPoincare
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductMorphisms

/-! # Dual Product Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.DualProductComparison

noncomputable section

/-! A normalized abelian group product carries its actual dual and
polarization to the constant special-fiber data. Normalization of the
dual is deduced from the Poincare class, and group compatibility follows
from the proved rigidity over complex dual numbers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of (DualNumber ℂ))))
    (e : A.abelian.scheme ≅ ((A.abelian.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).scheme)
    [heGroup : IsMonHom e.hom]

theorem polarizedDualProductComparison_normalized (he : NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e) :
    NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ (Abelian.DualProductComparison.abelianDualProductComparison A.abelian A.dual e) :=
  Dual.ProductNormalizationFromPoincare.dualProduct_normalized_of_poincare A e
    (Abelian.DualProductComparison.abelianDualProductComparison A.abelian A.dual e) he (DualProductPoincare.polarizedDualProductComparison_poincare A e)

theorem polarizedDualProductComparison_isMonHom (he : NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e) :
    IsMonHom (Abelian.DualProductComparison.abelianDualProductComparison A.abelian A.dual e).hom := by
  have : Smooth ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj A.dual.abelian.scheme).hom :=
    inferInstanceAs (Smooth (A.dual.abelian.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).scheme.hom)
  have : IsProper ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj A.dual.abelian.scheme).hom :=
    inferInstanceAs (IsProper (A.dual.abelian.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).scheme.hom)
  have : GeometricallyConnected ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj A.dual.abelian.scheme).hom :=
    inferInstanceAs (GeometricallyConnected (A.dual.abelian.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).scheme.hom)
  exact NormalizedDual.ProductGroupIso.pointedNormalizedDualProduct_isMonHom A.dual.abelian.scheme
    (Abelian.DualProductComparison.abelianDualProductComparison A.abelian A.dual e) (polarizedDualProductComparison_normalized A e he)
    (Abelian.DualProductComparison.abelianDualProductComparison_pointed A.abelian A.dual e)

theorem normalizedDualProduct_polarization (he : NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e) :
    A.polarization.isogeny.hom ≫ (Abelian.DualProductComparison.abelianDualProductComparison A.abelian A.dual e).hom =
      e.hom ≫ ((A.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).polarization.isogeny.hom := by
  have : Smooth ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj A.abelian.scheme).hom :=
    inferInstanceAs (Smooth (A.abelian.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).scheme.hom)
  have : IsProper ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj A.abelian.scheme).hom :=
    inferInstanceAs (IsProper (A.abelian.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).scheme.hom)
  have : GeometricallyConnected ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj A.abelian.scheme).hom :=
    inferInstanceAs (GeometricallyConnected (A.abelian.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).scheme.hom)
  have hdGroup := polarizedDualProductComparison_isMonHom A e he
  exact @NormalizedDual.ProductMorphisms.normalizedGroupDualProduct_morphism A.abelian.scheme A.dual.abelian.scheme _ _ _ _ _ e
    (Abelian.DualProductComparison.abelianDualProductComparison A.abelian A.dual e) heGroup hdGroup he
    (polarizedDualProductComparison_normalized A e he) A.polarization.isogeny.hom inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.DualProductComparison
