import OAI.ArithmeticGeometry.Descent.CMVariety.EnhancedParameterComplex
import OAI.ArithmeticGeometry.Descent.CMVariety.BaseChangeMaps
import OAI.ArithmeticGeometry.Descent.CMVariety.CountableNeighborhoodIsolation

/-! # Enhanced Parameter -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-!
The constructed parameter maps openly to its injective arithmetic chart.
Local constancy of the original moduli point therefore isolates that
chart point and gives the exact checked number-field descent conclusion.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Filter Set
open scoped _root_.Topology

variable {X : Scheme} {f : X ⟶ Spec (CommRingCat.of ℚ)}
  {g N r m : ℕ} {δ : Fin g → ℕ}
  {A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r X} {p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X}
  {k : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) (A.pullback p).polarized.abelian}
  (D : EnhancedChart.Abelian.SmoothEnhancedParameter f A p k)

def EnhancedChart.Abelian.SmoothEnhancedParameter.chartRationalStructure : Spec (CommRingCat.of D.chart.ring) ⟶ Spec (CommRingCat.of ℚ) :=
  D.chart.map ≫ f

instance EnhancedChart.Abelian.SmoothEnhancedParameter.chartRationalStructure_smooth : Smooth D.chartRationalStructure := by
  change Smooth (D.chart.map ≫ f)
  rw [D.chart.structure_eq]
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr D.chart.smooth)

theorem EnhancedChart.Abelian.SmoothEnhancedParameter.chartMap_structure : D.chartMap ≫ D.chartRationalStructure = D.map ≫ f := by
  change D.chartMap ≫ (D.chart.map ≫ f) = D.map ≫ f
  rw [← Category.assoc, ← D.map_eq]

def EnhancedChart.Abelian.SmoothEnhancedParameter.nativeChartBase : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase := ComplexParameter.Abelian.arithmeticComplexBase D.chartRationalStructure

instance EnhancedChart.Abelian.SmoothEnhancedParameter.nativeChartBase_smooth : Smooth D.nativeChartBase.hom := by
  change Smooth (pullback.snd D.chartRationalStructure (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
  infer_instance

def EnhancedChart.Abelian.SmoothEnhancedParameter.nativeChartCenter : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.nativeChartBase :=
  ComplexParameter.Abelian.arithmeticComplexPoint D.chartRationalStructure (Spec.map (CommRingCat.ofHom D.chart.point.toRingHom))

def EnhancedChart.Abelian.SmoothEnhancedParameter.nativeChartMap : D.nativeBase ⟶ D.nativeChartBase :=
  BaseChangeMaps.Abelian.arithmeticBaseChangeMap (D.map ≫ f) D.chartRationalStructure D.chartMap D.chartMap_structure

theorem EnhancedChart.Abelian.SmoothEnhancedParameter.nativeChartMap_isOpenMap : IsOpenMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map D.nativeChartMap) :=
  BaseChangeMaps.Abelian.arithmeticBaseChangeMap_isOpenMap (D.map ≫ f) D.chartRationalStructure D.chartMap D.chartMap_structure

theorem EnhancedChart.Abelian.SmoothEnhancedParameter.nativeChartMap_center :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map D.nativeChartMap D.nativeCenter = D.nativeChartCenter :=
  BaseChangeMaps.Abelian.arithmeticBaseChangeMap_point (D.map ≫ f) D.chartRationalStructure D.chartMap D.chartMap_structure
    D.point (Spec.map (CommRingCat.ofHom D.chart.point.toRingHom)) D.point_chart

def EnhancedChart.Abelian.SmoothEnhancedParameter.nativeChartPointMap (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.nativeChartBase) : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X :=
  s.left ≫ pullback.fst D.chartRationalStructure
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) ≫ D.chart.map

theorem EnhancedChart.Abelian.SmoothEnhancedParameter.nativeChartPointMap_injective : Function.Injective D.nativeChartPointMap :=
  ComplexParameter.Abelian.arithmeticComplexBase_pointMap_injective D.chartRationalStructure D.chart.map

theorem EnhancedChart.Abelian.SmoothEnhancedParameter.nativeChartCenter_original : D.nativeChartPointMap D.nativeChartCenter = p := by
  change D.nativeChartCenter.left ≫ pullback.fst D.chartRationalStructure
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) ≫ D.chart.map = p
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ D.chart.map)
      (ComplexParameter.Abelian.arithmeticComplexPoint_projection D.chartRationalStructure
        (Spec.map (CommRingCat.ofHom D.chart.point.toRingHom)))).trans D.chart.recovers)

theorem EnhancedChart.Abelian.SmoothEnhancedParameter.nativeChartPointMap_map (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.nativeBase) :
    D.nativeChartPointMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map D.nativeChartMap s) = D.nativePointMap s := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))
  let πX : D.nativeBase.left ⟶ D.space := pullback.fst (D.map ≫ f) c
  let πY : D.nativeChartBase.left ⟶ Spec (CommRingCat.of D.chart.ring) :=
    pullback.fst D.chartRationalStructure c
  let v : D.nativeBase.left ⟶ D.nativeChartBase.left := D.nativeChartMap.left
  have hv : v ≫ πY = πX ≫ D.chartMap :=
    BaseChangeMaps.Abelian.arithmeticBaseChangeMap_fst (D.map ≫ f) D.chartRationalStructure D.chartMap D.chartMap_structure
  change (s.left ≫ v) ≫ πY ≫ D.chart.map = (s.left ≫ πX) ≫ D.map
  calc
    (s.left ≫ v) ≫ πY ≫ D.chart.map = s.left ≫ (v ≫ πY) ≫ D.chart.map := by
      simp only [Category.assoc]
    _ = s.left ≫ (πX ≫ D.chartMap) ≫ D.chart.map :=
      congrArg (fun a => s.left ≫ a ≫ D.chart.map) hv
    _ = (s.left ≫ πX) ≫ (D.chartMap ≫ D.chart.map) := by simp only [Category.assoc]
    _ = (s.left ≫ πX) ≫ D.map := congrArg (fun a => (s.left ≫ πX) ≫ a) D.map_eq.symm

theorem EnhancedChart.Abelian.SmoothEnhancedParameter.numberField_of_native_chart_isolated
    (hopen : IsOpen ({D.nativeChartCenter} : Set (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.nativeChartBase))) :
    ∃ (K : Subfield ℂ), NumberField K ∧ ∃ pK : Spec (CommRingCat.of K) ⟶ X,
      Spec.map (CommRingCat.ofHom K.subtype) ≫ pK = p := by
  have hs := IntrinsicIsolatedPoint.Abelian.scheme_isolated_of_native_isolated D.nativeChartBase D.nativeChartCenter hopen
  obtain ⟨K, hK, qK, hqK⟩ := AlgebraicPoints.Abelian.complex_point_descends_of_isolated_baseChange
    D.chartRationalStructure D.nativeChartCenter.left hs
  refine ⟨K, hK, qK ≫ D.chart.map, ?_⟩
  rw [← Category.assoc, hqK]
  exact (Category.assoc _ _ _).trans D.nativeChartCenter_original

theorem EnhancedChart.Abelian.SmoothEnhancedParameter.numberField_of_eventually_constant_point_map
    (h : ∀ᶠ s in 𝓝 D.nativeCenter, D.nativePointMap s = p) :
    ∃ (K : Subfield ℂ), NumberField K ∧ ∃ pK : Spec (CommRingCat.of K) ⟶ X,
      Spec.map (CommRingCat.ofHom K.subtype) ≫ pK = p := by
  let U := {s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.nativeBase | D.nativePointMap s = p}
  have hU : U ∈ 𝓝 D.nativeCenter := h
  have himage : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map D.nativeChartMap '' U ∈ 𝓝 D.nativeChartCenter := by
    simpa only [D.nativeChartMap_center] using D.nativeChartMap_isOpenMap.image_mem_nhds hU
  have hsingle : ({D.nativeChartCenter} : Set (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.nativeChartBase)) ∈
      𝓝 D.nativeChartCenter := by
    apply mem_of_superset himage
    rintro _ ⟨s, hs, rfl⟩
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map D.nativeChartMap s = D.nativeChartCenter
    apply D.nativeChartPointMap_injective
    rw [D.nativeChartPointMap_map, D.nativeChartCenter_original]
    exact hs
  apply D.numberField_of_native_chart_isolated
  rw [isOpen_iff_mem_nhds]
  rintro s rfl
  exact hsingle

theorem EnhancedChart.Abelian.SmoothEnhancedParameter.numberField_of_countable_point_map_image
    {U : Set (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.nativeBase)} (hU : U ∈ 𝓝 D.nativeCenter)
    (hcount : (D.nativePointMap '' U).Countable) :
    ∃ (K : Subfield ℂ), NumberField K ∧ ∃ pK : Spec (CommRingCat.of K) ⟶ X,
      Spec.map (CommRingCat.ofHom K.subtype) ≫ pK = p := by
  let V := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map D.nativeChartMap '' U
  have hV : V ∈ 𝓝 D.nativeChartCenter := by
    simpa only [D.nativeChartMap_center] using D.nativeChartMap_isOpenMap.image_mem_nhds hU
  have hcV : V.Countable := by
    apply (hcount.preimage D.nativeChartPointMap_injective).mono
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, hs, (D.nativeChartPointMap_map s).symm⟩
  exact D.numberField_of_native_chart_isolated
    (CountableNeighborhoodIsolation.Abelian.native_isolated_of_countable_neighborhood D.nativeChartBase D.nativeChartCenter hV hcV)

end

end OAI.ArithmeticGeometry.Descent.CMVariety
