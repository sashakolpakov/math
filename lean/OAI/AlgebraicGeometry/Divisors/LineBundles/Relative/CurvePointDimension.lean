import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.DimensionGeneric
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.PushforwardDimensionDrop

/-! # Curve Point Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CurvePointDimension.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual divisor points contributing under a relative curve map lie over the generic point -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY] [LocallyOfFiniteType (f ≫ gY)]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ gY))

include hdim in
theorem relativeCurve_coheight_le_one (x : X) (hx : f x = genericPoint Y) : coheight x ≤ 1 := by
  let j := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)
  let : LocallyOfFiniteType ((j ≫ f) ≫ gY) := by
    rw [Category.assoc]
    infer_instance
  have hη : (j ≫ f) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x))) = genericPoint Y :=
    (congrArg f (Point.SupportNaturality.BundleCycles.pointSupport_genericPoint X x)).trans hx
  have hd := Cycles.Functoriality.FunctionFields.Construction.dimension_le_of_genericPoint (j ≫ f) hη gY
  rw [Category.assoc] at hd
  have hp : (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY : ℕ∞) ≤
      (Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY) : ℕ∞) := by
    exact_mod_cast hd
  have hp' : coheight x + (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY : ℕ∞) ≤
      coheight x + (Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY) : ℕ∞) :=
    add_le_add_right hp (coheight x)
  have hc := hp'.trans (Point.DimensionBound.BundleCycles.coheight_add_pointDimension_le (f ≫ gY) x)
  rw [← hdim, Nat.cast_add, Nat.cast_one, add_comm (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY : ℕ∞) 1] at hc
  exact (ENat.add_le_add_iff_right (by simp)).mp hc

include hdim in
theorem relativeCurve_divisor_image_generic [AlgebraicGeometry.IsNoetherian X]
    (x : X) (hx : coheight x = 1) (hdeg : f.residueDegree x ≠ 0) : f x = genericPoint Y := by
  apply Point.DimensionGeneric.BundleCycles.point_eq_generic_of_dimension_eq gY (f x)
  have hd := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one (f ≫ gY) x hx
  have he := Finite.GenericDimension.BundleCycles.pointClosure_dimension_of_nonzeroResidueDegree f gY x hdeg
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CurvePointDimension.BundleCycles
