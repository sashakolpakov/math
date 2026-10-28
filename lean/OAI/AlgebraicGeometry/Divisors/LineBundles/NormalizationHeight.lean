import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.Height
import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationCharts
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalNormalization

/-! # Normalization Height -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationHeight.BundleCycles

noncomputable section

/-! Normalization of an integral scheme locally of finite type over a field
preserves every point's codimension. The affine proof uses prime-height
preservation under the actual integral extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

universe u

theorem normalizationMap_coheight {k : Type u} [Field k]
    (X : Scheme.{u}) [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (y : IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) : coheight (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X y) = coheight y := by
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X y))
  let : Nonempty U := ⟨⟨IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X y, hxU⟩⟩
  let A := Γ(X, U)
  let B := integralClosure A X.functionField
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  have hinj : Function.Injective (algebraMap A B) :=
    IntersectionTheory.ProjectionFormula.SemilocalNormalization.algebraMap_injective A B X.functionField
  have hyrange : y ∈ Set.range (NormalizationCharts.BundleCycles.normalizationChartMap X U hU) := by
    rw [NormalizationCharts.BundleCycles.normalizationChartMap_range]
    exact hxU
  obtain ⟨q, hq⟩ := hyrange
  have hpoint := congrArg (fun i : Spec (.of B) ⟶ X => i q)
    (NormalizationCharts.BundleCycles.normalizationChartMap_comp X U hU)
  change IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X (NormalizationCharts.BundleCycles.normalizationChartMap X U hU q) =
    hU.fromSpec ((Spec.map (CommRingCat.ofHom (algebraMap A B))) q) at hpoint
  rw [← hq, hpoint]
  simp only [coheight_eq_of_isOpenImmersion]
  rw [← idealHeight_eq_coheight, ← idealHeight_eq_coheight]
  exact IntersectionTheory.ProjectionFormula.Integral.Height.integral_height_under k A B hinj q

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationHeight.BundleCycles
