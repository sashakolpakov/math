import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AffineCoordinatesM
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveSmoothTo
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme

/-! # Projective Coordinates M -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCoordinatesM.Constructions.ProjectiveCoordinates

noncomputable section

/-!
# Standard projective charts and the native complex manifold

The coordinate maps are built from the genuine polynomial affine chart
immersions and compared with the established regular-coordinate atlas.
-/

open scoped ContDiff _root_.Manifold _root_.Topology
open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion ChartedSpace Filter

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- A native regular chart has analytic transition to any chart coming from
a genuine affine open immersion. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.contDiffOn_regularChart_to_affineChart (A : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left] {n m : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (Fin n → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (he : e ∈ ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas X n) (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m) :
    ContDiffOn ℂ ω (e.symm.trans (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i f))
      (e.symm.trans (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i f)).source := by
  obtain ⟨V, hV, d, hd, rfl⟩ := he
  exact ComplexPoints.Analytic.AffineOpenTransitions.contDiffOn_affineOpenChartTransition
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V) A
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV) i d f hd hf

variable [IsIntegral X.left] [Smooth X.hom]

local notation "ModelX" =>
  (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

/-- Every actual regular affine chart is analytic on its source in the native
scheme manifold, including charts whose dimension is separately indexed. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.contMDiffAt_affineChartOnScheme (A : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left] {m : ℕ}
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m) {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X}
    (hx : x ∈ (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i f).source) :
    ContMDiffAt (𝓘(ℂ, ModelX)) (𝓘(ℂ, Fin m → ℂ)) ω
      (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i f) x := by
  let e := chartAt ModelX x
  let c := ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i f
  have hx' : e x ∈ (e.symm.trans c).source := by
    refine ⟨e.map_source (mem_chart_source _ x), ?_⟩
    change e.symm (e x) ∈ c.source
    rw [e.left_inv (mem_chart_source _ x)]
    exact hx
  have hd := (ProjectiveGraph.Constructions.ProjectiveCoordinates.contDiffOn_regularChart_to_affineChart A i e f
    (chart_mem_atlas _ x) hf).contDiffAt
    ((e.symm.trans c).open_source.mem_nhds hx')
  rw [contMDiffAt_iff_source]
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_iff_contDiffAt.mpr
  simpa only [extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    OpenPartialHomeomorph.coe_trans, Function.comp_def, id_eq, e] using hd

/-- The inverse of a regular affine chart is also analytic in the native
scheme manifold. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.contMDiffAt_affineChartOnScheme_symm (A : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left] {m : ℕ}
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m) {z : Fin m → ℂ} (hz : z ∈ f.target) :
    ContMDiffAt (𝓘(ℂ, Fin m → ℂ)) (𝓘(ℂ, ModelX)) ω
      (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i f).symm z := by
  let c := ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i f
  let e := chartAt ModelX (c.symm z)
  have hz' : z ∈ (c.symm.trans e).source :=
    ⟨hz, mem_chart_source _ _⟩
  have hd := (ComplexPoints.Analytic.AffineOpenDifferential.contDiffOn_affinePointMap_regularCharts A i f e hf
    (chart_mem_atlas _ (c.symm z))).contDiffAt
    ((c.symm.trans e).open_source.mem_nhds hz')
  rw [contMDiffAt_iff_target]
  refine ⟨c.continuousAt_symm hz, ?_⟩
  apply contMDiffAt_iff_contDiffAt.mpr
  simpa only [extChartAt_coe, modelWithCornersSelf_coe,
    Function.comp_def, id_eq, e, c, ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_symm_apply] using hd

theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiable_affineChartOnScheme (A : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left] {m : ℕ}
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m) :
    (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i f).MDifferentiable
      (𝓘(ℂ, ModelX)) (𝓘(ℂ, Fin m → ℂ)) := by
  constructor
  · intro x hx
    exact ((ProjectiveGraph.Constructions.ProjectiveCoordinates.contMDiffAt_affineChartOnScheme A i f hf hx).mdifferentiableAt
      (by simp)).mdifferentiableWithinAt
  · intro z hz
    exact ((ProjectiveGraph.Constructions.ProjectiveCoordinates.contMDiffAt_affineChartOnScheme_symm A i f hf hz).mdifferentiableAt
      (by simp)).mdifferentiableWithinAt

def _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.polynomialFinHomeomorph (n : ℕ) (i : Fin (n + 1)) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) ≃ₜ (Fin n → ℂ) :=
  (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i}).trans
    (Homeomorph.piCongrLeft (Y := fun _ : {j : Fin (n + 1) // j ≠ i} => ℂ)
      (finSuccAboveEquiv i)).symm

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.polynomialFinHomeomorph_symm_apply (n : ℕ) (i : Fin (n + 1))
    (z : Fin n → ℂ) (p : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) :
    (ProjectiveGraph.Constructions.ProjectiveCoordinates.polynomialFinHomeomorph n i).symm z p =
      MvPolynomial.eval (fun j => z ((finSuccAboveEquiv i).symm j)) p := by
  simp only [ProjectiveGraph.Constructions.ProjectiveCoordinates.polynomialFinHomeomorph, Homeomorph.symm_trans_apply,
    Homeomorph.symm_symm, ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph_symm_apply]
  congr 1
  apply congrArg MvPolynomial.eval
  funext j
  obtain ⟨k, rfl⟩ := (finSuccAboveEquiv i).surjective j
  simp only [Homeomorph.piCongrLeft_apply_apply, Equiv.symm_apply_apply]

theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.polynomialFinHomeomorph_mem_regularAtlas (n : ℕ) (i : Fin (n + 1)) :
    (ProjectiveGraph.Constructions.ProjectiveCoordinates.polynomialFinHomeomorph n i).toOpenPartialHomeomorph ∈
      ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) n := by
  constructor
  · intro p
    simpa only [Homeomorph.toOpenPartialHomeomorph_target,
      Homeomorph.toOpenPartialHomeomorph_symm_apply,
      ProjectiveGraph.Constructions.ProjectiveCoordinates.polynomialFinHomeomorph_symm_apply, ContinuousLinearMap.proj_apply] using
      (AnalyticOnNhd.eval_continuousLinearMap'
      (fun j => (ContinuousLinearMap.proj ((finSuccAboveEquiv i).symm j) :
        (Fin n → ℂ) →L[ℂ] ℂ)) p).contDiffOn
        uniqueDiffOn_univ (n := ω)
  · refine ⟨1, ?_, ?_⟩
    · intro x _
      simp
    · intro j
      refine ⟨MvPolynomial.X (finSuccAboveEquiv i j), 0, ?_⟩
      intro x _
      change x (MvPolynomial.X (finSuccAboveEquiv i j)) = _
      simp

/-- The standard projective coordinate chart, constructed through the actual
open immersion of the polynomial affine scheme. -/
def _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart (n : ℕ) (i : Fin (n + 1)) :
    OpenPartialHomeomorph (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n) (Fin n → ℂ) :=
  ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (CommAlgCat.of ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))
    (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap n i)
    (ProjectiveGraph.Constructions.ProjectiveCoordinates.polynomialFinHomeomorph n i).toOpenPartialHomeomorph

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart_target (n : ℕ) (i : Fin (n + 1)) :
    (ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i).target = Set.univ := rfl

/-- The genuine scheme chart inverse is the ordinary projective chart inverse
under the established scheme-point homeomorphism. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart_symm (n : ℕ) (i : Fin (n + 1)) (z : Fin n → ℂ) :
    (ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i).symm z =
      ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n ((ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm z) := by
  simp only [ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart, ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_symm_apply,
    Homeomorph.toOpenPartialHomeomorph_symm_apply, ProjectiveGraph.Constructions.ProjectiveCoordinates.polynomialFinHomeomorph,
    Homeomorph.symm_trans_apply, Homeomorph.symm_symm]
  change ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint n i _ = _
  rw [ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint_eq_projectivization]
  simp only [ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart, OpenPartialHomeomorph.transHomeomorph,
    ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph_apply]
  rfl

theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart_apply (n : ℕ) (i : Fin (n + 1))
    (p : Projectivization ℂ (Fin (n + 1) → ℂ))
    (hp : p ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
    ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n p) =
      ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i p := by
  have h := ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart_symm n i (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i p)
  rw [(ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).left_inv hp] at h
  rw [← h]
  exact (ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i).right_inv (Set.mem_univ _)

theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mem_nativeProjectiveChart_source (n : ℕ) (i : Fin (n + 1))
    (p : Projectivization ℂ (Fin (n + 1) → ℂ))
    (hp : p ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
    ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n p ∈ (ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i).source := by
  have h := ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart_symm n i (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i p)
  rw [(ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).left_inv hp] at h
  rw [← h]
  exact (ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i).map_target (Set.mem_univ _)

local instance (n : ℕ) : IsIntegral (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).left :=
  ProjectiveSmoothTo.Constructions.ProjectiveSmooth.isIntegral_projectiveSpace n

local instance (n : ℕ) : IsIntegral (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :=
  ProjectiveSmoothTo.Constructions.ProjectiveSmooth.isIntegral_projectiveSpace n

local instance (n : ℕ) : Smooth (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).hom :=
  ProjectiveSmoothTo.Constructions.ProjectiveSmooth.smooth_projectiveSpaceToBase n

abbrev _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.NativeModel (n : ℕ) :=
  Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension
    (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).hom) → ℂ

theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.contMDiffAt_nativeProjectiveChart (n : ℕ) (i : Fin (n + 1))
    {x : ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n} (hx : x ∈ (ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i).source) :
    ContMDiffAt (𝓘(ℂ, ProjectiveGraph.Constructions.ProjectiveCoordinates.NativeModel n)) (𝓘(ℂ, Fin n → ℂ)) ω
      (ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i) x :=
  ProjectiveGraph.Constructions.ProjectiveCoordinates.contMDiffAt_affineChartOnScheme _ _ _ (ProjectiveGraph.Constructions.ProjectiveCoordinates.polynomialFinHomeomorph_mem_regularAtlas n i) hx

theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiable_nativeProjectiveChart (n : ℕ) (i : Fin (n + 1)) :
    (ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i).MDifferentiable
      (𝓘(ℂ, ProjectiveGraph.Constructions.ProjectiveCoordinates.NativeModel n)) (𝓘(ℂ, Fin n → ℂ)) :=
  ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiable_affineChartOnScheme _ _ _ (ProjectiveGraph.Constructions.ProjectiveCoordinates.polynomialFinHomeomorph_mem_regularAtlas n i)

theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mfderiv_nativeProjectiveChart_bijective (n : ℕ) (i : Fin (n + 1))
    {x : ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n} (hx : x ∈ (ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i).source) :
    Function.Bijective (mfderiv (𝓘(ℂ, ProjectiveGraph.Constructions.ProjectiveCoordinates.NativeModel n)) (𝓘(ℂ, Fin n → ℂ))
      (ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i) x) :=
  (ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiable_nativeProjectiveChart n i).mfderiv_bijective hx

/-- Standard affine coordinates of an actual algebraic map into projective
space, on its usual nonvanishing-coordinate patch. -/
def _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap {n : ℕ}
    (φ : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (i : Fin (n + 1))
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : Fin n → ℂ :=
  ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ x))

omit [IsIntegral X.left] [Smooth X.hom] in
theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap_eventuallyEq_native {n : ℕ}
    (φ : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (i : Fin (n + 1))
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X}
    (hx : (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ x) ∈
      (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
    ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap φ i =ᶠ[𝓝 x]
      (fun y => ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ y)) := by
  have hc := (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm.continuous.comp
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map φ)
  filter_upwards [((ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).open_source.preimage hc).mem_nhds hx] with y hy
  simpa only [Homeomorph.apply_symm_apply, ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap] using
    (ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart_apply n i
      ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ y)) hy).symm

theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiableAt_coordinatesOfSchemeMap {n : ℕ}
    (φ : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (i : Fin (n + 1))
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X}
    (hx : (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ x) ∈
      (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
    MDifferentiableAt (𝓘(ℂ, ModelX)) (𝓘(ℂ, Fin n → ℂ))
      (ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap φ i) x := by
  have hx' : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ x ∈ (ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i).source := by
    simpa only [Homeomorph.apply_symm_apply] using
      ProjectiveGraph.Constructions.ProjectiveCoordinates.mem_nativeProjectiveChart_source n i _ hx
  have hd := ((ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiable_nativeProjectiveChart n i).mdifferentiableAt hx').comp x
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map φ 1).mdifferentiableAt one_ne_zero)
  exact hd.congr_of_eventuallyEq (ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap_eventuallyEq_native φ i hx)

/-- The derivative of a genuine projective closed immersion is injective
in standard affine projective coordinates. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mfderiv_coordinatesOfSchemeMap_injective {n : ℕ}
    (φ : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsClosedImmersion φ.left]
    (i : Fin (n + 1)) {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X}
    (hx : (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ x) ∈
      (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
    Function.Injective (mfderiv (𝓘(ℂ, ModelX)) (𝓘(ℂ, Fin n → ℂ))
      (ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap φ i) x) := by
  have hx' : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ x ∈ (ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i).source := by
    simpa only [Homeomorph.apply_symm_apply] using
      ProjectiveGraph.Constructions.ProjectiveCoordinates.mem_nativeProjectiveChart_source n i _ hx
  rw [(ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap_eventuallyEq_native φ i hx).mfderiv_eq]
  rw [show (fun y => ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ y)) =
    (ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i) ∘ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) from rfl]
  rw [mfderiv_comp x
    ((ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiable_nativeProjectiveChart n i).mdifferentiableAt hx')
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map φ 1).mdifferentiableAt one_ne_zero)]
  exact (ProjectiveGraph.Constructions.ProjectiveCoordinates.mfderiv_nativeProjectiveChart_bijective n i hx').1.comp
    (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.mfderiv_nativeScheme_closedImmersion_injective φ x)

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCoordinatesM.Constructions.ProjectiveCoordinates
