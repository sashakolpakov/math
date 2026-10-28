import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TypeElevenBilinear

/-! # Riemann Form -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm

noncomputable section

/-! A positive Hermitian form on the native tangent space, constructed
from the original ample Chern class, with its actual rational periods. -/

def nativeRiemannForm (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple) :
    A.variety.analyticModel →ₗ⋆[ℂ] A.variety.analyticModel →ₗ[ℂ] ℂ :=
  TypeElevenBilinear.typeElevenHermitian (AmpleChernInvariant.nativeChernCovector A L) (AmpleChernInvariant.nativeChernCovector_pure A L hL)

theorem nativeRiemannForm_symmetry (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple) (u v : A.variety.analyticModel) :
    nativeRiemannForm A L hL v u = star (nativeRiemannForm A L hL u v) :=
  TypeElevenBilinear.typeElevenHermitian_symmetry (AmpleChernInvariant.nativeChernCovector A L) (AmpleChernInvariant.nativeChernCovector_pure A L hL) u v

theorem nativeRiemannForm_positive (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple) (u : A.variety.analyticModel) (hu : u ≠ 0) :
    0 < (nativeRiemannForm A L hL u u).re :=
  TypeElevenBilinear.typeElevenHermitian_positive (AmpleChernInvariant.nativeChernCovector A L) (AmpleChernInvariant.nativeChernCovector_pure A L hL)
    (AmpleChernInvariant.nativeChernCovector_positive_model A L hL) u hu

theorem nativeRiemannForm_imaginary (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple) (u v : A.variety.analyticModel) :
    (nativeRiemannForm A L hL u v).im = (AmpleChernInvariant.nativeChernCovector A L ![u, v]).re :=
  TypeElevenBilinear.realCovectorBilinear_apply (AmpleChernInvariant.nativeChernCovector A L) u v

theorem nativeRiemannForm_period (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple) (v w : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    (nativeRiemannForm A L hL v.val w.val).im = (ChernPairing.nativeChernForm A L v w : ℝ) :=
  (nativeRiemannForm_imaginary A L hL v.val w.val).trans
    ((congrArg Complex.re (ChernPeriod.nativeChernForm_covector A L v w)).trans (Complex.ratCast_re _))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm
