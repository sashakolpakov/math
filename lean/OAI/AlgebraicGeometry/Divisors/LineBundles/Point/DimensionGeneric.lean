import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop

/-! # Dimension Generic -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.DimensionGeneric.BundleCycles

noncomputable section

/-! # LineBundleCycles: only the actual generic point has a point closure of full dimension -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem point_eq_generic_of_dimension_eq {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (x : X)
    (hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f) :
    x = genericPoint X := by
  let W := CycleClass.Geometric.StratumClosure.integralImageClosure (𝟙 X)
  have hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
    have h := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure (𝟙 X) f
    rw [Category.id_comp] at h
    exact h.symm
  have hle : irreducibleSetEquivPoints.symm x ≤ W := by
    change closure {x} ⊆ closure (Set.range (𝟙 X))
    simp
  have he : irreducibleSetEquivPoints.symm x = W := by
    by_contra hn
    have h := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono f (lt_of_le_of_ne hle hn)
    change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f <
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f at h
    omega
  have hp := congrArg irreducibleSetEquivPoints he
  rw [irreducibleSetEquivPoints.apply_symm_apply] at hp
  exact hp.trans (Integral.ClosedImage.BundleCycles.integralClosedImage_genericPoint (𝟙 X))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.DimensionGeneric.BundleCycles
