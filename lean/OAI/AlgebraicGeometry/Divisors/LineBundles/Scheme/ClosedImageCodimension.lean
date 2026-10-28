import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportAnalyticImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImageDimension

/-! # Closed Image Codimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedImageCodimension.BundleCycles

noncomputable section

/-! A closed immersion preserves every support dimension, hence adds its actual ambient codimension to the cycle codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (Z : IrreducibleCloseds X.left)

omit [LocallyOfFiniteType X.hom] in
theorem schemeClosedImage_supportDimension :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) Y.hom = Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom := by
  have hd := Integral.ClosedImageDimension.BundleCycles.integralClosedImage_dimension (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ i.left) Y.hom
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) Y.hom =
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ((CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ i.left) ≫ Y.hom) at hd
  rw [Category.assoc, i.w] at hd
  exact hd

variable [IsIntegral X.left] [IsIntegral Y.left] [Smooth X.hom] [Smooth Y.hom]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (q : ℕ) (hq : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

include hp hq in
omit [Smooth X.hom] [Smooth Y.hom] in
theorem schemeClosedImage_codimension :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) Y.hom + (p + q) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom := by
  rw [schemeClosedImage_supportDimension i Z]
  have hX := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension X.hom
  have hY := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension Y.hom
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedImageCodimension.BundleCycles
