import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.ProductSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ProductChart

/-! # Product Over -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.ProductOver.BundleCycles

noncomputable section

/-! The genuine Laurent product over the complex base, including its native smooth fiber and topology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

def complexLaurentOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (LaurentPolynomial ℂ)

instance complexLaurentOver_integral : IsIntegral complexLaurentOver.left :=
  inferInstanceAs (IsIntegral (Spec (CommRingCat.of (LaurentPolynomial ℂ))))

instance complexLaurentOver_smooth : Smooth complexLaurentOver.hom := ProjectionSmooth.BundleCycles.laurentProjection_smooth ℂ

instance complexLaurentOver_metrizable : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints complexLaurentOver) := by
  let : IsSeparated complexLaurentOver.hom :=
    inferInstanceAs (IsSeparated (FiberGenericPoint.BundleCycles.laurentProjection ℂ))
  let : QuasiCompact complexLaurentOver.hom :=
    inferInstanceAs (QuasiCompact (FiberGenericPoint.BundleCycles.laurentProjection ℂ))
  exact CycleClass.Thom.SeparatedSchemeTopology.Constructions.schemePoints_metrizable complexLaurentOver

variable (R : Type) [CommRing R] [Algebra ℂ R]

def laurentFiberMap : Spec (CommRingCat.of (LaurentPolynomial R)) ⟶ complexLaurentOver.left :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ (algebraMap ℂ R)))

def laurentProductOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (laurentFiberMap R ≫ complexLaurentOver.hom)

def laurentFiberOver : laurentProductOver R ⟶ complexLaurentOver := Over.homMk (laurentFiberMap R) rfl

def laurentProjectionOver : laurentProductOver R ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R :=
  Over.homMk (FiberGenericPoint.BundleCycles.laurentProjection R) (ProductSquare.BundleCycles.laurentProjection_isPullback ℂ R).w

def laurentProductIsLimit : IsLimit (BinaryFan.mk (laurentFiberOver R) (laurentProjectionOver R)) :=
  (ProductSquare.BundleCycles.laurentProjection_isPullback ℂ R).flip.isLimit.pullbackConeEquivBinaryFanFunctor

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.ProductOver.BundleCycles
