import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticOpenDensity
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCoordinatesM
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveSubscheme
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldFinite
import OAI.AlgebraicGeometry.ComplexPoints.SchemeClosed
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothImmersion

/-! # Compact Analytic Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactAnalyticOpen

noncomputable section

/-!
A compact nonempty analytic open in a smooth integral complex scheme with a
projective immersion is the whole analytification. The native differential of
the immersion gives homogeneous equations for its compact analytic image;
analytic-open density then identifies that image with the original scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothImmersion Set
open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions
open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCoordinatesM.Constructions.ProjectiveCoordinates
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open scoped ContDiff _root_.Manifold _root_.Topology

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]

local notation "ModelX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

local instance (n : ℕ) : IsIntegral (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).left :=
  ComplexGroups.HolomorphicAlgebraicity.ProjectiveSmoothTo.Constructions.ProjectiveSmooth.isIntegral_projectiveSpace n

local instance (n : ℕ) : Smooth (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).hom :=
  ComplexGroups.HolomorphicAlgebraicity.ProjectiveSmoothTo.Constructions.ProjectiveSmooth.smooth_projectiveSpaceToBase n

def projectiveImmersionPointMap {n : ℕ}
    (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → Projectivization ℂ (Fin (n + 1) → ℂ) :=
  fun x => (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x)

theorem projectiveImmersion_coordinates_injective {n : ℕ}
    (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsImmersion f.left]
    (i : Fin (n + 1)) {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X}
    (hx : projectiveImmersionPointMap f x ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
    Function.Injective (mfderiv (𝓘(ℂ, ModelX)) (𝓘(ℂ, Fin n → ℂ))
      (ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap f i) x) := by
  have hx' : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x ∈ (ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i).source := by
    simpa only [projectiveImmersionPointMap, Homeomorph.apply_symm_apply] using
      ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mem_nativeProjectiveChart_source n i _ hx
  rw [(ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap_eventuallyEq_native f i hx).mfderiv_eq]
  rw [show (fun y => ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f y)) =
    (ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.nativeProjectiveChart n i) ∘ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) from rfl]
  rw [mfderiv_comp x
    ((ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiable_nativeProjectiveChart n i).mdifferentiableAt hx')
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map f 1).mdifferentiableAt one_ne_zero)]
  exact (ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mfderiv_nativeProjectiveChart_bijective n i hx').1.comp
    (ComplexPoints.Analytic.IntrinsicSmoothImmersion.mfderiv_nativeScheme_immersion_injective f x)

theorem projectiveImmersion_chart_data {n : ℕ}
    (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsImmersion f.left]
    (i : Fin (n + 1)) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hx : x ∈ Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartDomain (projectiveImmersionPointMap f) i) :
    MDifferentiableAt (𝓘(ℂ, ModelX)) (𝓘(ℂ, {j : Fin (n + 1) // j ≠ i} → ℂ))
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartMap (projectiveImmersionPointMap f) i) x ∧
    Function.Injective (mfderiv (𝓘(ℂ, ModelX)) (𝓘(ℂ, {j : Fin (n + 1) // j ≠ i} → ℂ))
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartMap (projectiveImmersionPointMap f) i) x) := by
  have he : Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartMap (projectiveImmersionPointMap f) i =
      (ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.expandFin i) ∘ ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap f i := by
    funext y
    exact (ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.expandFin_projectiveFinChart i _).symm
  have hc := ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiableAt_coordinatesOfSchemeMap f i hx
  have hl := (mdifferentiable_iff_differentiable.mpr (ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.expandFin i).differentiable)
    (ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap f i x)
  rw [he]
  refine ⟨hl.comp x hc, ?_⟩
  rw [mfderiv_comp x hl hc, mfderiv_eq_fderiv, (ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.expandFin i).fderiv]
  exact (ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.contractFin_expandFin i).injective.comp
    (projectiveImmersion_coordinates_injective f i hx)

private theorem analyticOpen_inclusion_mfderiv_injective
    (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (x : U) :
    Function.Injective (mfderiv (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelX))
      (Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) x) := by
  have hd : (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).MDifferentiable
      (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelX)) := by
    constructor
    · exact (contMDiff_subtype_val (I := 𝓘(ℂ, ModelX)) (U := U) (n := ω)).mdifferentiable
        (by simp) |>.mdifferentiableOn
    · intro y hy
      have hyU : y ∈ (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) := by
        simpa only [Opens.openPartialHomeomorphSubtypeCoe_target] using hy
      have hg : ContMDiffAt (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelX)) ∞
          (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).symm y := by
        rw [← ContMDiffAt.subtypeVal_comp_iff]
        apply contMDiffAt_id.congr_of_eventuallyEq
        filter_upwards [U.isOpen.mem_nhds hyU] with z hz
        exact (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).right_inv
          (by simpa only [Opens.openPartialHomeomorphSubtypeCoe_target] using hz)
      exact (hg.mdifferentiableAt (by simp)).mdifferentiableWithinAt
  exact (hd.mfderiv_bijective (x := x) (by trivial)).1

def analyticOpenProjectivePointMap {n : ℕ}
    (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) : U → Projectivization ℂ (Fin (n + 1) → ℂ) :=
  fun x => projectiveImmersionPointMap f x.val

theorem analyticOpenProjective_chart_data {n : ℕ}
    (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsImmersion f.left]
    (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (i : Fin (n + 1)) (x : U)
    (hx : x ∈ Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartDomain (analyticOpenProjectivePointMap f U) i) :
    MDifferentiableAt (𝓘(ℂ, ModelX)) (𝓘(ℂ, {j : Fin (n + 1) // j ≠ i} → ℂ))
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartMap (analyticOpenProjectivePointMap f U) i) x ∧
    Function.Injective (mfderiv (𝓘(ℂ, ModelX)) (𝓘(ℂ, {j : Fin (n + 1) // j ≠ i} → ℂ))
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartMap (analyticOpenProjectivePointMap f U) i) x) := by
  have hd := projectiveImmersion_chart_data f i x.val hx
  have hsub := ((contMDiff_subtype_val (I := 𝓘(ℂ, ModelX)) (U := U) (n := ω)) x).mdifferentiableAt
    (by simp)
  have he : Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartMap (analyticOpenProjectivePointMap f U) i =
      Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartMap (projectiveImmersionPointMap f) i ∘ (Subtype.val : U → _) := rfl
  rw [he]
  refine ⟨hd.1.comp x hsub, ?_⟩
  rw [mfderiv_comp x hd.1 hsub]
  exact hd.2.comp (analyticOpen_inclusion_mfderiv_injective U x)

theorem compact_analyticOpen_projective_equations {n : ℕ}
    (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsImmersion f.left]
    (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) [Nonempty U] [CompactSpace U] :
    ∃ Q : Finset (MvPolynomial (Fin (n + 1)) ℂ),
      (∀ q ∈ Q, ∃ d, q.IsHomogeneous d) ∧
      ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range (analyticOpenProjectivePointMap f U)) =
        {v | ∀ q ∈ Q, MvPolynomial.eval v q = 0} := by
  have hb : Topology.IsEmbedding (projectiveImmersionPointMap f) :=
    (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm.isEmbedding.comp
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion f)
  have hc : Continuous (analyticOpenProjectivePointMap f U) :=
    hb.continuous.comp continuous_subtype_val
  have hi : Function.Injective (analyticOpenProjectivePointMap f U) :=
    hb.injective.comp Subtype.val_injective
  have he : Topology.IsClosedEmbedding (analyticOpenProjectivePointMap f U) :=
    .of_continuous_injective_isClosedMap hc hi hc.isClosedMap
  exact Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldFinite.Constructions.ProjectiveManifoldEquations.finite_homogeneous_equations
    (analyticOpenProjectivePointMap f U) he (analyticOpenProjective_chart_data f U)

variable {n : ℕ} (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsImmersion f.left]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) [Nonempty U] [CompactSpace U]

include f U

theorem compact_analyticOpen_has_closed_projective_image :
    ∃ (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (j : Z ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)),
      IsClosedImmersion j.left ∧
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f '' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) =
          range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) := by
  classical
  obtain ⟨Q, hQ, hcone⟩ := compact_analyticOpen_projective_equations f U
  choose degree hdegree using fun q : Q => hQ q.val q.property
  have hzero : range (analyticOpenProjectivePointMap f U) =
      Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus (fun q : Q => q.val) degree hdegree := by
    ext p
    have he : p.rep ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range (analyticOpenProjectivePointMap f U)) ↔
        ∀ q ∈ Q, MvPolynomial.eval p.rep q = 0 := by
      rw [hcone]
      rfl
    rw [ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.mem_projectiveCone_iff _ p.rep p.rep_nonzero, p.mk_rep] at he
    rw [← p.mk_rep, Foundations.Scheme.ProjectiveZeroLocus.mem_projectiveCommonZeroLocus_mk]
    simpa only [p.mk_rep, Subtype.forall] using he
  obtain ⟨Z, j, _hZ, hj, _hproper, himage⟩ :=
    ComplexGroups.HolomorphicAlgebraicity.ProjectiveSubscheme.Constructions.Algebraization.exists_reduced_projective_subscheme_of_equations
      (fun q : Q => q.val) degree hdegree
  refine ⟨Z, j, hj, ?_⟩
  ext z
  let p := (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm z
  have hp : Foundations.Scheme.ProjectiveComplexPoints.projectiveComplexPointsEquiv n p = z :=
    (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).apply_symm_apply z
  have hz : z ∈ range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) ↔
      p ∈ Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus (fun q : Q => q.val) degree hdegree := by
    simpa only [hp] using himage p
  rw [hz, ← hzero]
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨⟨x, hx⟩, congrArg (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm he⟩
  · rintro ⟨x, hx⟩
    exact ⟨x.val, x.property, (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm.injective hx⟩

theorem compact_analyticOpen_eq_univ_of_projective_immersion :
    (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) = univ := by
  obtain ⟨Z, j, hj, himage⟩ := compact_analyticOpen_has_closed_projective_image f U
  let : IsClosedImmersion j.left := hj
  have hUn : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty U›
    exact ⟨x.val, x.property⟩
  exact AnalyticOpenDensity.analytic_open_eq_univ_of_closed_image f j U U.isOpen hUn himage

theorem compactSpace_of_compact_analyticOpen_projective_immersion :
    CompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
  have hc : IsCompact (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) := isCompact_iff_compactSpace.mpr inferInstance
  rw [compact_analyticOpen_eq_univ_of_projective_immersion f U] at hc
  exact isCompact_univ_iff.mp hc

theorem projectiveImmersion_isClosed_of_compact_analyticOpen : IsClosedImmersion f.left := by
  let : CompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
    compactSpace_of_compact_analyticOpen_projective_immersion f U
  let : LocallyOfFiniteType (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).hom :=
    (Foundations.Scheme.ClosedProjective.projectiveSpaceToBase_finiteType n).1
  exact ComplexPoints.SchemeClosed.ClosednessConstruction.immersion_isClosedImmersion_of_analytic_image f
    (isCompact_range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map f)).isClosed

def projectivePresentation_of_compact_analyticOpen : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom where
  ambientDimension := n
  embedding := f.left
  closedImmersion := projectiveImmersion_isClosed_of_compact_analyticOpen f U
  over_base := f.w

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactAnalyticOpen
