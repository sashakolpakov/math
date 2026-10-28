import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedAtlasOpenGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.MixedCenterChart

/-! # Mixed Center Coordinate Chart -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Resolution.Blowups.Global

/-! Native common-center atlases assembled from actual affine open charts through every point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (I : X.IdealSheafData) {β : Type} (D : β → X.IdealSheafData) where
  ring : CommRingCat
  algebra : Algebra ℂ ring
  map : Spec ring ⟶ X
  isOpenImmersion : IsOpenImmersion map
  ground : map ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure ring
  centerIdeal : Ideal ring
  center_eq : I.comap map = Affine.QuotientKernel.Construction.affineQuotientKernel centerIdeal
  equations : β → ring
  boundary_eq : ∀ l, (D l).comap map = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {equations l})
  divided : Finset β
  boundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ ring equations
  center : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts ℂ ring centerIdeal equations divided

attribute [instance] MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart.algebra MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart.isOpenImmersion

def MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart.ofNativeCoordinateChart
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    {β : Type} (D : β → X.IdealSheafData) (U : X.affineOpens)
    (w : β → Γ(X, U)) (hw : ∀ l, (D l).ideal U = Ideal.span {w l})
    (F : Finset β) (p : PrimeSpectrum Γ(X, U)) :
    letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart ℂ (.of Γ(X, U)) (I.ideal U) w F p →
      MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart f I D := by
  let : Algebra ℂ Γ(X, U) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  intro C
  refine {
    ring := C.chart.carrier
    algebra := C.chart.algebra
    map := Spec.map (CommRingCat.ofHom C.chart.map.toRingHom) ≫ U.2.fromSpec
    isOpenImmersion := inferInstance
    ground := ?_
    centerIdeal := (I.ideal U).map C.chart.map.toRingHom
    center_eq := Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel I U C.chart.map.toRingHom
    equations := fun l => C.chart.map (w l)
    boundary_eq := ?_
    divided := F
    boundary := C.chart.model.hasEtaleBoundaryCharts
    center := by
      rw [C.center_eq]
      exact C.chart.model.hasMixedCenterCharts C.coordinates F C.divided_iff }
  · rw [Category.assoc, ← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U, ← Spec.map_comp]
    apply congrArg Spec.map
    ext c
    exact C.chart.map.commutes c
  · intro l
    have h := Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel (D l) U C.chart.map.toRingHom
    rw [hw, Ideal.map_span, Set.image_singleton] at h
    exact h

def MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart.ofAtlas
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} {D : β → X.IdealSheafData} (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (i : A.indices) :
    MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart f I D := by
  let U := A.opens i
  let : Algebra ℂ Γ(X, U) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  exact {
    ring := Γ(X, U)
    algebra := inferInstance
    map := U.2.fromSpec
    isOpenImmersion := U.2.isOpenImmersion_fromSpec
    ground := (Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U).symm
    centerIdeal := I.ideal U
    center_eq := Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel I U
    equations := A.equations i
    boundary_eq := fun l => (Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel (D l) U).trans
      (congrArg Affine.QuotientKernel.Construction.affineQuotientKernel (A.component i l))
    divided := A.divided i
    boundary := A.boundary i
    center := A.center i }

def MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart.comp
    {V X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    {β : Type} (D : β → X.IdealSheafData) (j : V ⟶ X) [IsOpenImmersion j]
    (C : MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart (j ≫ f) (I.comap j) (fun l => (D l).comap j)) :
    MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart f I D where
  ring := C.ring
  algebra := C.algebra
  map := C.map ≫ j
  isOpenImmersion := inferInstance
  ground := (Category.assoc _ _ _).trans C.ground
  centerIdeal := C.centerIdeal
  center_eq := (Scheme.IdealSheafData.comap_comp I C.map j).trans C.center_eq
  equations := C.equations
  boundary_eq l := (Scheme.IdealSheafData.comap_comp (D l) C.map j).trans (C.boundary_eq l)
  divided := C.divided
  boundary := C.boundary
  center := C.center

def CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofPointedCharts
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    {β : Type} (D : β → X.IdealSheafData)
    (h : ∀ x : X, ∃ C : MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart f I D,
      ∃ p : PrimeSpectrum C.ring, C.map p = x) : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D := by
  choose C p hp using h
  let Q : X.AffineOpenCover := {
    I₀ := X
    X := fun x => (C x).ring
    f := fun x => (C x).map
    map_prop := fun x => (C x).isOpenImmersion
    idx := id
    covers := fun x => ⟨p x, hp x⟩ }
  let : ∀ x : Q.I₀, Algebra ℂ (Q.X x) := fun x => (C x).algebra
  exact CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofAffineCover f I D Q (fun x => (C x).ground)
    (fun x => (C x).centerIdeal) (fun x => (C x).equations) (fun x => (C x).divided)
    (fun x => (C x).center_eq) (fun x => (C x).boundary_eq)
    (fun x => (C x).boundary) (fun x => (C x).center)

end AlgebraicGeometry.Resolution.Blowups.Global

namespace AlgebraicGeometry.Resolution.Blowups.Global.MixedCenterCoordinateChart.Construction

/-! Pointed coordinate charts over arbitrary actual affine opens give native global center charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def GlobalMixedCenterOpenChart.ofCoordinateChart
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    {β : Type} (D : β → X.IdealSheafData) (R : CommRingCat) [Algebra ℂ R]
    (j : Spec R ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (K : Ideal R)
    (hK : I.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K)
    (w : β → R) (hw : ∀ l, (D l).comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w l}))
    (F : Finset β) (p : PrimeSpectrum R)
    (C : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart ℂ R K w F p) :
    GlobalMixedCenterOpenChart f I D := by
  let : Algebra ℂ C.chart.carrier := C.chart.algebra
  refine {
    ring := C.chart.carrier
    algebra := C.chart.algebra
    map := Spec.map (CommRingCat.ofHom C.chart.map.toRingHom) ≫ j
    isOpenImmersion := inferInstance
    ground := ?_
    centerIdeal := K.map C.chart.map.toRingHom
    center_eq := ?_
    equations := fun l => C.chart.map (w l)
    boundary_eq := ?_
    divided := F
    boundary := C.chart.model.hasEtaleBoundaryCharts
    center := by
      rw [C.center_eq]
      exact C.chart.model.hasMixedCenterCharts C.coordinates F C.divided_iff }
  · rw [Category.assoc, hj]
    change Spec.map (CommRingCat.ofHom C.chart.map.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ C.chart.carrier))
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext c
    exact C.chart.map.commutes c
  · rw [Scheme.IdealSheafData.comap_comp, hK, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  · intro l
    rw [Scheme.IdealSheafData.comap_comp, hw l, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom,
      Ideal.map_span, Set.image_singleton]

end AlgebraicGeometry.Resolution.Blowups.Global.MixedCenterCoordinateChart.Construction

end

end OAI
