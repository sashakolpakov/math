import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.ModeledNormalChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizationRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PointedSmoothCenter

/-! # Normal Chart Intrinsic Data -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Modeled normal-chart equations provide the native carrier, smoothness, full boundary atlas, and maximal contact. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
  {β : Type} {D : β → X.IdealSheafData} {x : X}

def GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart.nativeCarrier (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart f J n D x) :
    (Spec C.ring).IdealSheafData := Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C.normal})

theorem GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart.nativeCarrier_smooth (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart f J n D x) :
    Smooth (C.nativeCarrier.subschemeι ≫ (C.map ≫ f)) := by
  rw [C.ground]
  let : Algebra.Smooth ℂ (C.ring ⧸ Ideal.span {C.normal}) := C.coefficientBoundary.smooth
  exact Global.PointedSmoothCenter.Construction.affineQuotientKernel_complex_subscheme_smooth C.ring (Ideal.span {C.normal})

def GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart.native_boundaryAtlas [Fintype β] (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart f J n D x) :
    Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (C.map ≫ f)
      (fun i : Option β => match i with | none => C.nativeCarrier | some l => (D l).comap C.map) [Finset.univ] := by
  rw [C.ground]
  let A := Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.ofAffineEquations C.ring
    (fun i : Option β => match i with | none => C.normal | some l => C.equations l) C.fullBoundary
  have he : (fun i : Option β => match i with | none => C.nativeCarrier | some l => (D l).comap C.map) =
      (fun i => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {match i with | none => C.normal | some l => C.equations l})) := by
    funext i
    cases i with
    | none => rfl
    | some l => exact C.component l
  rw [he]
  exact A

theorem GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart.homogenized_restrict [Smooth f] (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart f J n D x) :
    (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C.map = Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ C.ideal n) :=
  Global.HomogenizationRestriction.Construction.smoothHomogenizedIdealSheaf_comap_affine f J n C.map C.ground C.ideal C.ideal_eq

theorem GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart.nativeCarrier_tangent [Smooth f] (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryNormalChart f J n D x) :
    C.nativeCarrier ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (C.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C.map) n := by
  rw [DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (C.map ≫ f) (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure C.ring) C.ground,
    C.homogenized_restrict, ComplexAffineDifferentialIdeal.Construction.smoothDifferentialIdealSheaf_affineQuotientKernel,
    HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent]
  exact Global.DifferentialTransform.Construction.affineQuotientKernel_mono ((Ideal.span_singleton_le_iff_mem
    (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ C.ideal n)).mpr C.normal_mem)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
