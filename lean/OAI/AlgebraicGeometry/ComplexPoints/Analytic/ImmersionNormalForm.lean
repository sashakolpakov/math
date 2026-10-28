import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.LinearImmersionComplement
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionChartDerivative
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionComplementDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Immersion Normal Form -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionNormalForm

noncomputable section

/-!
# Analytic normal forms from injective differentials

The normal coordinates are constructed by adjoining complementary linear
directions to the given map and applying the genuine inverse function theorem.
No implication from an injective differential to an immersion is assumed.
-/

open scoped ContDiff _root_.Manifold _root_.Topology
open Filter Set

section InverseFunctionConstruction

variable {K E F : Type*} [RCLike K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup F] [NormedSpace K F]

/-- Adjoin actual complementary target directions to a nonlinear map. -/
def immersionExtension (f : E → F) (C : Submodule K F) (z : E × C) : F :=
  f z.1 + (z.2 : F)

/-- The extension's differential is the original differential together with
the inclusion of the complementary directions. -/
theorem hasFDerivAt_immersionExtension (f : E → F) (C : Submodule K F)
    (L : E →L[K] F) (x : E) (hf : HasFDerivAt f L x) :
    HasFDerivAt (immersionExtension f C)
      (L.comp (ContinuousLinearMap.fst K E C) +
        C.subtypeL.comp (ContinuousLinearMap.snd K E C)) (x, 0) :=
  (hf.comp (x, 0) hasFDerivAt_fst).add
    (C.subtypeL.hasFDerivAt.comp (x, 0) hasFDerivAt_snd)

/-- The extension is analytic whenever the original map is analytic. -/
theorem contDiffAt_immersionExtension (f : E → F) (C : Submodule K F)
    (x : E) {n : ℕ∞ω} (hf : ContDiffAt K n f x) :
    ContDiffAt K n (immersionExtension f C) (x, 0) :=
  (hf.comp (x, 0) contDiffAt_fst).add
    (C.subtypeL.contDiff.contDiffAt.comp (x, 0) contDiffAt_snd)

variable [FiniteDimensional K E] [FiniteDimensional K F]

/-- The inverse function theorem turns a proved linear complement into
actual analytic normal coordinates, with both maps analytic on their domains. -/
theorem exists_analytic_immersionExtension_chart (f : E → F) (x : E)
    (hf : ContDiffAt K ω f x) (C : Submodule K F)
    (e : (E × C) ≃L[K] F)
    (he : ∀ z : E × C, e z = fderiv K f x z.1 + (z.2 : F)) :
    ∃ q : OpenPartialHomeomorph (E × C) F,
      (x, 0) ∈ q.source ∧
      (q : E × C → F) = immersionExtension f C ∧
      ContDiffOn K ω q q.source ∧ ContDiffOn K ω q.symm q.target := by
  let := FiniteDimensional.complete K (E × C)
  have hd := hasFDerivAt_immersionExtension f C (fderiv K f x) x
    (hf.differentiableAt (by simp)).hasFDerivAt
  have heq : (fderiv K f x).comp (ContinuousLinearMap.fst K E C) +
      C.subtypeL.comp (ContinuousLinearMap.snd K E C) = e.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro z
    exact (he z).symm
  rw [heq] at hd
  have hg := contDiffAt_immersionExtension f C x hf
  let q₀ := hg.toOpenPartialHomeomorph (immersionExtension f C) hd (by simp)
  have hx : (x, (0 : C)) ∈ q₀.source :=
    hg.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hi : ContDiffAt K ω q₀.symm (q₀ (x, 0)) :=
    hg.to_localInverse hd (by simp)
  refine ⟨q₀.restrContDiff K ω (by simp), ?_, rfl, ?_, ?_⟩
  · change (x, (0 : C)) ∈ q₀.source ∩
      {z | ContDiffAt K ω q₀ z ∧ ContDiffAt K ω q₀.symm (q₀ z)}
    exact ⟨hx, hg, hi⟩
  · exact q₀.contDiffOn_restrContDiff_source K (by simp)
  · exact q₀.contDiffOn_restrContDiff_target K (by simp)

end InverseFunctionConstruction

section EuclideanNormalForm

variable {K E F C : Type*} [RCLike K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup F] [NormedSpace K F]
variable [NormedAddCommGroup C] [NormedSpace K C]

/-- An analytic inverse-function chart whose zero slice is the original map
gives the standard manifold immersion normal form. -/
theorem isImmersionAtOfComplement_of_normal_chart
    (f : E → F) (x : E) (e : (E × C) ≃L[K] F)
    (q : OpenPartialHomeomorph (E × C) F)
    (hx : (x, 0) ∈ q.source) (hzero : ∀ y, q (y, 0) = f y)
    (hq : ContDiffOn K ω q q.source)
    (hqi : ContDiffOn K ω q.symm q.target) :
    Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, F) ω f x := by
  let U : Set E := (fun y : E => (y, (0 : C))) ⁻¹' q.source
  have hU : IsOpen U := q.open_source.preimage (continuous_id.prodMk continuous_const)
  let dom : OpenPartialHomeomorph E E := OpenPartialHomeomorph.ofSet U hU
  let cod : OpenPartialHomeomorph F F := q.symm.transHomeomorph e.toHomeomorph
  have hdom : dom ∈ IsManifold.maximalAtlas 𝓘(K, E) ω E := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact contMDiff_id.contMDiffOn
    · exact contMDiff_id.contMDiffOn
  have hcod : cod ∈ IsManifold.maximalAtlas 𝓘(K, F) ω F := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · apply ContDiffOn.contMDiffOn
      exact e.contDiff.comp_contDiffOn hqi
    · apply ContDiffOn.contMDiffOn
      exact hq.comp e.symm.contDiff.contDiffOn (fun _ hz => hz)
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts e dom cod hx ?_
    hdom hcod ?_ ?_
  · change f x ∈ q.target
    rw [← hzero x]
    exact q.map_source hx
  · intro y hy
    change f y ∈ q.target
    rw [← hzero y]
    exact q.map_source hy
  · intro y hy
    have hy' : (y, (0 : C)) ∈ q.source := by
      have : y ∈ dom.target := by
        simpa only [OpenPartialHomeomorph.extend_target, modelWithCornersSelf_coe,
          modelWithCornersSelf_coe_symm, Set.range_id, Set.preimage_id,
          Set.inter_univ] using hy
      exact this
    change e (q.symm (f y)) = e (y, 0)
    rw [← hzero y, q.left_inv hy']

variable [FiniteDimensional K E] [FiniteDimensional K F]

/-- In finite dimensions, an injective derivative of an analytic map yields
genuine analytic manifold immersion charts. -/
theorem isImmersionAt_of_injective_fderiv (f : E → F) (x : E)
    (hf : ContDiffAt K ω f x) (hi : Function.Injective (fderiv K f x)) :
    Manifold.IsImmersionAt 𝓘(K, E) 𝓘(K, F) ω f x := by
  obtain ⟨C, e, he⟩ := LinearImmersionComplement.exists_linearImmersionComplement (fderiv K f x) hi
  obtain ⟨q, hx, hqf, hq, hqi⟩ :=
    exists_analytic_immersionExtension_chart f x hf C e he
  have hzero : ∀ y, q (y, 0) = f y := by
    intro y
    rw [hqf]
    simp only [immersionExtension, ZeroMemClass.coe_zero, add_zero]
  exact (isImmersionAtOfComplement_of_normal_chart f x e q hx hzero hq hqi).isImmersionAt

end EuclideanNormalForm

section ChartTransport

variable {K E : Type*} [RCLike K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
variable {n : ℕ∞ω} [IsManifold 𝓘(K, E) n M]

/-- Composition with an actual smooth model-space coordinate change stays
in the same maximal atlas. -/
theorem mem_maximalAtlas_trans_self
    (c : OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph E E)
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(K, E) n M)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(K, E) n E) :
    c.trans d ∈ IsManifold.maximalAtlas 𝓘(K, E) n M := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (contMDiffOn_of_mem_maximalAtlas hd).comp'
      (contMDiffOn_of_mem_maximalAtlas hc)
  · exact (contMDiffOn_symm_of_mem_maximalAtlas hc).comp'
      (contMDiffOn_symm_of_mem_maximalAtlas hd)

variable {F N : Type*} [NormedAddCommGroup F] [NormedSpace K F]
variable [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(K, F) n N]

/-- A normal form constructed in genuine manifold coordinates transports
back to a normal form on the manifolds themselves. -/
theorem isImmersionAt_of_coordinate_normal_form
    (f : M → N) (x : M) (c : OpenPartialHomeomorph M E)
    (d : OpenPartialHomeomorph N F)
    (hx : x ∈ c.source) (hfx : f x ∈ d.source)
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(K, E) n M)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(K, F) n N)
    (hf : ContinuousAt f x)
    (h : Manifold.IsImmersionAt 𝓘(K, E) 𝓘(K, F) n
      (d ∘ f ∘ c.symm) (c x)) :
    Manifold.IsImmersionAt 𝓘(K, E) 𝓘(K, F) n f x := by
  apply Manifold.IsImmersionAt.mk_of_continuousAt hf h.equiv
    (c.trans h.domChart) (d.trans h.codChart)
  · exact ⟨hx, h.mem_domChart_source⟩
  · refine ⟨hfx, ?_⟩
    change d (f x) ∈ h.codChart.source
    simpa only [Function.comp_apply, c.left_inv hx] using h.mem_codChart_source
  · exact mem_maximalAtlas_trans_self c h.domChart hc h.domChart_mem_maximalAtlas
  · exact mem_maximalAtlas_trans_self d h.codChart hd h.codChart_mem_maximalAtlas
  · intro z hz
    have hzt : z ∈ (c.trans h.domChart).target := by
      simpa only [OpenPartialHomeomorph.extend_target, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Set.range_id, Set.preimage_id,
        Set.inter_univ] using hz
    have hzd : z ∈ (h.domChart.extend 𝓘(K, E)).target := by
      simpa only [OpenPartialHomeomorph.extend_target, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Set.range_id, Set.preimage_id,
        Set.inter_univ] using hzt.1
    exact h.writtenInCharts hzd

end ChartTransport

section InjectiveManifoldDifferential

variable {K E F M N : Type*} [RCLike K]
variable [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
variable [NormedAddCommGroup F] [NormedSpace K F] [FiniteDimensional K F]
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(K, E) ω M]
variable [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(K, F) ω N]

/-- An injective actual manifold differential gives genuine analytic normal
charts. The coordinate derivative is identified with the manifold derivative,
then a complement and the inverse function theorem construct those charts. -/
theorem isImmersionAt_of_injective_mfderiv (f : M → N) (x : M)
    (hf : ContMDiffAt 𝓘(K, E) 𝓘(K, F) ω f x)
    (hi : Function.Injective (mfderiv 𝓘(K, E) 𝓘(K, F) f x)) :
    Manifold.IsImmersionAt 𝓘(K, E) 𝓘(K, F) ω f x := by
  apply isImmersionAt_of_coordinate_normal_form f x (chartAt E x) (chartAt F (f x))
    (mem_chart_source E x) (mem_chart_source F (f x))
    (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (f x))
    hf.continuousAt
  exact isImmersionAt_of_injective_fderiv (ImmersionChartDerivative.preferredChartMap (E := E) (F := F) f x)
    (chartAt E x x) (ImmersionChartDerivative.contDiffAt_preferredChartMap hf)
    (ImmersionChartDerivative.preferredChartDerivative_injective hf (by simp) hi)

/-- In finite dimensions, an analytic map with injective manifold
differential everywhere is a global immersion with one fixed complement. -/
theorem isImmersion_of_injective_mfderiv (f : M → N)
    (hf : ContMDiff 𝓘(K, E) 𝓘(K, F) ω f)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(K, E) 𝓘(K, F) f x)) :
    Manifold.IsImmersion 𝓘(K, E) 𝓘(K, F) ω f :=
  ImmersionComplementDimension.isImmersion_of_forall_isImmersionAt
    (fun x => isImmersionAt_of_injective_mfderiv f x (hf x) (hi x))

end InjectiveManifoldDifferential

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)

/-- An actual immersion of smooth integral complex schemes has analytic
normal charts on its native complex-point manifolds. -/
theorem nativeScheme_isImmersionAt (φ : X ⟶ Y) [AlgebraicGeometry.IsImmersion φ.left]
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Manifold.IsImmersionAt 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelY) ω (SchemePointHomeomorphs.schemeComplexPoints.map φ) x :=
  isImmersionAt_of_injective_mfderiv (SchemePointHomeomorphs.schemeComplexPoints.map φ) x
    (IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map φ ω x) (IntrinsicSmoothImmersion.mfderiv_nativeScheme_immersion_injective φ x)

/-- The same native immersion admits genuine real analytic normal charts. -/
theorem real_nativeScheme_isImmersionAt (φ : X ⟶ Y)
    [AlgebraicGeometry.IsImmersion φ.left] (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Manifold.IsImmersionAt 𝓘(ℝ, ModelX) 𝓘(ℝ, ModelY) ω (SchemePointHomeomorphs.schemeComplexPoints.map φ) x :=
  isImmersionAt_of_injective_mfderiv (SchemePointHomeomorphs.schemeComplexPoints.map φ) x
    (IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map φ ω x) (IntrinsicSmoothImmersion.real_mfderiv_nativeScheme_immersion_injective φ x)

/-- Native complex points of an actual algebraic immersion have a fixed
normal model of precisely the difference in algebraic dimensions. -/
theorem nativeScheme_isImmersionOfComplement (φ : X ⟶ Y)
    [AlgebraicGeometry.IsImmersion φ.left] :
    Manifold.IsImmersionOfComplement
      (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom -
        Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
      𝓘(ℂ, ModelX) 𝓘(ℂ, ModelY) ω (SchemePointHomeomorphs.schemeComplexPoints.map φ) := by
  intro x
  let h := nativeScheme_isImmersionAt φ x
  let := ImmersionComplementDimension.immersionComplement_finiteDimensional h
  let e : h.complement ≃L[ℂ]
      (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom -
        Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by
      rw [ImmersionComplementDimension.immersionComplement_finrank h]
      simp only [Module.finrank_fin_fun])
  exact h.isImmersionAtOfComplement_complement.trans_F e

/-- Actual scheme immersions realize as genuine complex analytic manifold
immersions, including mathlib's requirement of one global normal model. -/
theorem nativeScheme_isImmersion (φ : X ⟶ Y) [AlgebraicGeometry.IsImmersion φ.left] :
    Manifold.IsImmersion 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelY) ω (SchemePointHomeomorphs.schemeComplexPoints.map φ) :=
  (nativeScheme_isImmersionOfComplement φ).isImmersion

/-- The underlying native real manifolds likewise form a genuine global
real analytic immersion. -/
theorem real_nativeScheme_isImmersion (φ : X ⟶ Y)
    [AlgebraicGeometry.IsImmersion φ.left] :
    Manifold.IsImmersion 𝓘(ℝ, ModelX) 𝓘(ℝ, ModelY) ω (SchemePointHomeomorphs.schemeComplexPoints.map φ) :=
  ImmersionComplementDimension.isImmersion_of_forall_isImmersionAt (real_nativeScheme_isImmersionAt φ)

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionNormalForm
