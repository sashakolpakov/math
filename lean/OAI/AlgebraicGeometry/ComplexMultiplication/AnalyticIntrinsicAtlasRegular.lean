import OAI.AlgebraicGeometry.ComplexMultiplication.PointBettiBridge
import OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicRegularCoordinates
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOverlap

/-! # Analytic Intrinsic Atlas Regular -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.AnalyticIntrinsicAtlasRegular

noncomputable section

section

/-! # Analytic transitions from the original atlas to the actual native atlas

The point comparison is the identity on the unchanged scheme-valued points.
The transitions use the actual ambient sections defining the native coordinates.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

/-- The existing identity point comparison, as a homeomorphism of the actual spaces. -/
def complexPointIdentityHomeomorph (X : Over (Spec (.of ℂ))) :
    Betti.Scheme.schemePointSpace X ≃ₜ ComplexPoint.Basic.ComplexSchemePoint X :=
  TopCat.homeoOfIso (PointBettiBridge.complexPointSpaceIso X)

/-- A genuine native chart transported along the identity point homeomorphism. -/
def nativeChartOnOriginal (X : Over (Spec (.of ℂ))) {n : ℕ}
    (c : OpenPartialHomeomorph (Betti.Scheme.schemePointSpace X) (Fin n → ℂ)) :
    OpenPartialHomeomorph (ComplexPoint.Basic.ComplexSchemePoint X) (Fin n → ℂ) :=
  (complexPointIdentityHomeomorph X).symm.transOpenPartialHomeomorph c

@[simp]
theorem nativeChartOnOriginal_apply (X : Over (Spec (.of ℂ))) {n : ℕ}
    (c : OpenPartialHomeomorph (Betti.Scheme.schemePointSpace X) (Fin n → ℂ))
    (q : ComplexPoint.Basic.ComplexSchemePoint X) : nativeChartOnOriginal X c q = c q := rfl

@[simp]
theorem nativeChartOnOriginal_symm_apply (X : Over (Spec (.of ℂ))) {n : ℕ}
    (c : OpenPartialHomeomorph (Betti.Scheme.schemePointSpace X) (Fin n → ℂ))
    (w : Fin n → ℂ) : (nativeChartOnOriginal X c).symm w = c.symm w := rfl

@[simp]
theorem nativeChartOnOriginal_source (X : Over (Spec (.of ℂ))) {n : ℕ}
    (c : OpenPartialHomeomorph (Betti.Scheme.schemePointSpace X) (Fin n → ℂ)) :
    (nativeChartOnOriginal X c).source = c.source := by
  ext q
  rfl

/-- A point in an actual affine-open chart belongs to the original ambient open. -/
theorem nativeAffineChart_source_mem (X : Over (Spec (.of ℂ)))
    (U : X.left.Opens) (hU : IsAffineOpen U) {n : ℕ}
    (e : OpenPartialHomeomorph
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (Fin n → ℂ))
    (q : Betti.Scheme.schemePointSpace X)
    (hq : q ∈ (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e).source) :
    q ∈ ComplexPoint.Basic.Point.overOpen U := by
  obtain ⟨x, _, rfl⟩ := hq
  change (ComplexPoint.Basic.Point.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) x)).underlying ∈ U
  rw [ComplexPoint.Basic.Point.underlying_map]
  have hmem (p : Spec (.of Γ(X.left, U))) : hU.fromSpec p ∈ U := by
    have hp : p ∈ hU.fromSpec ⁻¹ᵁ U := by
      rw [hU.fromSpec_preimage_self]
      trivial
    exact hp
  exact hmem _

/-- Transitions from the unchanged original charts to genuine native regular charts are analytic. -/
theorem contDiffOn_original_to_nativeChart
    (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom] {n : ℕ}
    (z : ComplexPoint.Basic.ComplexSchemePoint X)
    (c : OpenPartialHomeomorph (Betti.Scheme.schemePointSpace X) (Fin n → ℂ))
    (hc : c ∈ ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas X n) :
    ContDiffOn ℂ ω ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm.trans (nativeChartOnOriginal X c))
      ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm.trans (nativeChartOnOriginal X c)).source := by
  obtain ⟨U, hU, e, he, rfl⟩ := hc
  let c := ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e
  obtain ⟨g, hg, hcoords⟩ := IntrinsicRegularCoordinates.nativeAffineChart_regularCoordinates X U hU e he
  apply contDiffOn_pi.mpr
  intro i
  obtain ⟨a, k, hcoord⟩ := hcoords i
  have hr := IntrinsicRegularCoordinates.contDiffOn_originalChart_regularRatio X z U a g k
  have hdom : ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm.trans
      (nativeChartOnOriginal X c)).source ⊆
      {w | w ∈ (ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).target ∧
        (ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm w ∈ ComplexPoint.Basic.Point.overOpen U ∧
        ComplexPoint.Basic.Point.evaluate U g ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm w) ≠ 0} := by
    intro w hw
    have hq : (ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm w ∈ c.source := hw.2
    exact ⟨hw.1, nativeAffineChart_source_mem X U hU e _ hq, hg _ hq⟩
  apply (hr.mono hdom).congr
  intro w hw
  have hq : (ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z).symm w ∈ c.source := hw.2
  exact hcoord _ hq

end

section

/-! # Original regular sections are analytic in actual native affine charts

The formula is the original stalk evaluation. Local affine factorizations
express it as fractions of actual source regular-function evaluations.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Topology

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

/-- Both actual point conventions send the unique point of Spec ℂ to the same scheme point. -/
theorem nativeUnderlying_eq_original (X : Over (Spec (.of ℂ))) (q : ComplexPoint.Basic.ComplexSchemePoint X) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying q = ComplexPoint.Basic.Point.underlying q := by
  change q.left ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint = q.left _
  exact congrArg q.left (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _)

/-- Original evaluation on an affine open is analytic in genuine native affine coordinates. -/
theorem contDiffAt_nativeAffineChart_evaluate_affine
    (X : Over (Spec (.of ℂ))) (U V : X.left.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) {n : ℕ}
    (e : OpenPartialHomeomorph
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) n)
    (s : Γ(X.left, V)) (w : Fin n → ℂ) (hw : w ∈ e.target)
    (hv : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU (e.symm w) ∈
      ComplexPoint.Basic.Point.overOpen V) :
    ContDiffAt ℂ ω
      (fun v => ComplexPoint.Basic.Point.evaluate V s
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU (e.symm v))) w := by
  let A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U
  let B := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V
  let i := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU
  let j := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV
  have hq : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm w) ∈
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j) := by
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU (e.symm w) ∈
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X V hV)
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap]
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying _ ∈ V
    rw [nativeUnderlying_eq_original]
    exact hv
  obtain ⟨a, ha, h, _hfac, hpoint⟩ :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineLocalizationTransition A B i j (e.symm w) hq
  let v : (Fin n → ℂ) → B → ℂ := fun z b =>
    e.symm z (IsLocalization.Away.sec a (h b)).1 /
      (e.symm z a) ^ (IsLocalization.Away.sec a (h b)).2
  have hval (z : Fin n → ℂ) (hz : e.symm z a ≠ 0) (b : B) :
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h
        ⟨e.symm z, hz⟩ b = v z b :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition_eval A B a h
      ⟨e.symm z, hz⟩ b
  have hvat (b : B) : ContDiffAt ℂ ω (fun z => v z b) w :=
    ((he.1 (IsLocalization.Away.sec a (h b)).1).contDiffAt
      (e.open_target.mem_nhds hw)).div
      (((he.1 a).contDiffAt (e.open_target.mem_nhds hw)).pow
        (IsLocalization.Away.sec a (h b)).2)
      (pow_ne_zero _ ha)
  apply (hvat s).congr_of_eventuallyEq
  have hna : ∀ᶠ z in 𝓝 w, e.symm z a ≠ 0 :=
    ((he.1 a).contDiffAt (e.open_target.mem_nhds hw)).continuousAt.eventually_ne ha
  filter_upwards [hna] with z hz
  have hp := hpoint ⟨e.symm z, hz⟩
  have hvz : ComplexPoint.Basic.Point.evaluate V s
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z)) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h
        ⟨e.symm z, hz⟩ s := by
    rw [← hp]
    exact RegularSectionBridge.evaluate_nativeAffineOpenPoint X V hV _ s
  exact hvz.trans (hval z hz s)

end

section

/-! # Arbitrary original regular sections in the actual native atlas

An affine neighborhood of the evaluation point suffices. Restriction of the
original section preserves its stalk evaluation on that neighborhood.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Topology

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

/-- The original evaluation of any regular section is analytic in actual native coordinates. -/
theorem contDiffAt_nativeChartOnOriginal_evaluate
    (X : Over (Spec (.of ℂ))) (V : X.left.Opens) (s : Γ(X.left, V)) {n : ℕ}
    (c : OpenPartialHomeomorph (Betti.Scheme.schemePointSpace X) (Fin n → ℂ))
    (hc : c ∈ ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas X n)
    (w : Fin n → ℂ) (hw : w ∈ (nativeChartOnOriginal X c).target)
    (hv : (nativeChartOnOriginal X c).symm w ∈ ComplexPoint.Basic.Point.overOpen V) :
    ContDiffAt ℂ ω
      (fun v => ComplexPoint.Basic.Point.evaluate V s ((nativeChartOnOriginal X c).symm v)) w := by
  obtain ⟨U, hU, e, he, rfl⟩ := hc
  let c := ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e
  let c₀ := nativeChartOnOriginal X c
  obtain ⟨W, hW, hqW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (show (c₀.symm w).underlying ∈ V from hv)
  let t := X.left.presheaf.map (homOfLE (show W ≤ V from hWV)).op s
  let D := c₀.target ∩ {v | c₀.symm v ∈ ComplexPoint.Basic.Point.overOpen W}
  have hD : IsOpen D := c₀.isOpen_inter_preimage_symm (ComplexPoint.Basic.Point.isOpen_overOpen (X := X) W)
  have hwD : w ∈ D := ⟨hw, hqW⟩
  have ht : ContDiffAt ℂ ω
      (fun v => ComplexPoint.Basic.Point.evaluate W t (c₀.symm v)) w :=
    contDiffAt_nativeAffineChart_evaluate_affine X U W hU hW e he t w hw hqW
  apply ht.congr_of_eventuallyEq
  filter_upwards [hD.mem_nhds hwD] with v hvD
  exact ComplexPoint.Basic.Point.evaluate_res (show W ≤ V from hWV) s (c₀.symm v) hvD.2

end

section

/-! # Analytic transitions from the actual native atlas to the original atlas

The original coordinates are evaluations of their unchanged actual ambient
regular sections. Those evaluations are analytic in every native regular chart.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Topology

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

/-- Transitions from genuine native regular charts to unchanged original charts are analytic. -/
theorem contDiffOn_native_to_originalChart
    (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom] {n : ℕ}
    (z : ComplexPoint.Basic.ComplexSchemePoint X)
    (c : OpenPartialHomeomorph (Betti.Scheme.schemePointSpace X) (Fin n → ℂ))
    (hc : c ∈ ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas X n) :
    ContDiffOn ℂ ω ((nativeChartOnOriginal X c).symm.trans (ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z))
      ((nativeChartOnOriginal X c).symm.trans (ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z)).source := by
  let D := ((nativeChartOnOriginal X c).symm.trans (ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z)).source
  have hD : IsOpen D :=
    ((nativeChartOnOriginal X c).symm.trans (ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z)).open_source
  let E := ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z
  apply contDiffOn_pi.mpr
  intro i w hw
  have hV : (nativeChartOnOriginal X c).symm w ∈ ComplexPoint.Basic.Point.overOpen E.ambientCoordinateOpen := by
    have hmem := ComplexPoint.Basic.ComplexSchemePoint.mem_coordinateNeighborhood_of_mem_localChart_source X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)
      z ((nativeChartOnOriginal X c).symm w) hw.2
    simpa only [E, ComplexPoint.SmoothCoordinates.LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hmem
  have hi := contDiffAt_nativeChartOnOriginal_evaluate X E.ambientCoordinateOpen
    (E.ambientCoordinateSection i) c hc w hw.1 hV
  apply ContDiffAt.contDiffWithinAt
  apply hi.congr_of_eventuallyEq
  filter_upwards [hD.mem_nhds hw] with v hv
  exact ComplexPoint.Basic.ComplexSchemePoint.localChart_apply_component_eq_evaluate X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z
    ((nativeChartOnOriginal X c).symm v) hv.2 i

end

/-! # The identity between the two actual complex manifolds is analytic

A copy of the unchanged point carrier keeps the two charted-space instances
explicit. Its topology and atlas are precisely the existing native ones.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace ChartedSpace
open scoped ContDiff _root_.Manifold

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

/-- The unchanged actual point carrier, carrying the actual native manifold structure. -/
def NativePointManifold (X : Over (Spec (.of ℂ))) : Type := Betti.Scheme.schemePointSpace X

instance nativePointManifoldTopology (X : Over (Spec (.of ℂ))) :
    TopologicalSpace (NativePointManifold X) := (Betti.Scheme.schemePointSpace X).str

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "NativeModel" =>
  (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "OriginalModel" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)

instance nativePointManifoldChartedSpace : ChartedSpace NativeModel (NativePointManifold X) :=
  ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace X

instance nativePointManifoldIsManifold (r : ℕ∞ω) :
    IsManifold 𝓘(ℂ, NativeModel) r (NativePointManifold X) :=
  ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold X r

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The actual identity point comparison with both topologies explicitly retained. -/
def nativePointManifoldHomeomorph : NativePointManifold X ≃ₜ ComplexPoint.Basic.ComplexSchemePoint X :=
  complexPointIdentityHomeomorph X

/-- The actual identity from the native complex manifold to the original one is analytic. -/
theorem contMDiff_nativePointManifoldHomeomorph (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, NativeModel) 𝓘(ℂ, OriginalModel) r
      (nativePointManifoldHomeomorph X) := by
  apply contMDiff_iff.mpr
  refine ⟨(nativePointManifoldHomeomorph X).continuous, ?_⟩
  intro x y
  let c : OpenPartialHomeomorph (Betti.Scheme.schemePointSpace X) NativeModel :=
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace X).chartAt x
  have hc : c ∈ ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas X
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) :=
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace X).chart_mem_atlas x
  have h := (contDiffOn_native_to_originalChart X y c hc).of_le
    (show r ≤ ω from le_top)
  simp only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, Set.preimage, Set.mem_ofPred_eq, Set.ofPred_mem_eq,
    id_eq, Set.range_id, Set.inter_univ]
  change ContDiffOn ℂ r
    ((nativeChartOnOriginal X c).symm.trans (ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) y))
    ((nativeChartOnOriginal X c).symm.trans (ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) y)).source
  exact h

/-- The inverse actual identity from the original manifold to the native one is analytic. -/
theorem contMDiff_nativePointManifoldHomeomorph_symm (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, OriginalModel) 𝓘(ℂ, NativeModel) r
      (nativePointManifoldHomeomorph X).symm := by
  apply contMDiff_iff.mpr
  refine ⟨(nativePointManifoldHomeomorph X).continuous_invFun, ?_⟩
  intro x y
  let c : OpenPartialHomeomorph (Betti.Scheme.schemePointSpace X) NativeModel :=
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace X).chartAt y
  have hc : c ∈ ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas X
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) :=
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace X).chart_mem_atlas y
  have h := (contDiffOn_original_to_nativeChart X x c hc).of_le
    (show r ≤ ω from le_top)
  simp only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, Set.preimage, Set.mem_ofPred_eq, Set.ofPred_mem_eq,
    id_eq, Set.range_id, Set.inter_univ]
  change ContDiffOn ℂ r
    ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) x).symm.trans (nativeChartOnOriginal X c))
    ((ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) x).symm.trans (nativeChartOnOriginal X c)).source
  exact h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.AnalyticIntrinsicAtlasRegular
