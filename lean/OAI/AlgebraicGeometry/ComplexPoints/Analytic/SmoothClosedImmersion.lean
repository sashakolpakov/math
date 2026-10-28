import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineMaps
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ClosedImmersionPointTopology
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! # Smooth Closed Immersion -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion

noncomputable section

/-!
# Differentials of genuine affine closed immersions

A surjective map of complex coordinate rings induces an injective differential
on the native smooth affine point manifolds. The local proof lifts the source
chart's regular coordinate functions through the ring map and thereby constructs
an analytic left inverse to the map in actual regular coordinates.
-/

open scoped ContDiff _root_.Manifold _root_.Topology
open Filter

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
variable {n m : ℕ}

/-- The genuine chart overlap for a map of affine characters is a neighborhood
of a point belonging to both charts. -/
theorem affineChartComap_neighborhood
    (h : A →ₐ[ℂ] B)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source)
    (hfx : x.comp h ∈ f.source) :
    e.target ∩ {z | (e.symm z).comp h ∈ f.source} ∈ 𝓝 (e x) := by
  refine inter_mem (e.open_target.mem_nhds (e.map_source hx)) ?_
  have hc := (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h).continuous.continuousAt.comp
    (e.continuousAt_symm (e.map_source hx))
  have hh : f.source ∈ 𝓝 ((e.symm (e x)).comp h) := by
    rw [e.left_inv hx]
    exact f.open_source.mem_nhds hfx
  exact hc hh

/-- The map induced by a coordinate-ring homomorphism is analytic when written
in the concrete regular coordinate charts, at any point of their overlap. -/
theorem contDiffAt_affineChartComap
    (h : A →ₐ[ℂ] B)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (he : e ∈ SmoothSchemeManifold.affineRegularAtlas B n) (hf : f ∈ SmoothSchemeManifold.affineRegularAtlas A m)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source)
    (hfx : x.comp h ∈ f.source) :
    ContDiffAt ℂ ω (fun z => f ((e.symm z).comp h)) (e x) := by
  obtain ⟨g, hg, hcoords⟩ := hf.2
  exact (SmoothSchemeManifold.contDiffOn_affineChartComapTransition h e f he.1 g hg hcoords).contDiffAt
    (affineChartComap_neighborhood h e f x hx hfx)

/-- Surjectivity of the actual coordinate-ring map supplies a local analytic
left inverse in regular coordinates. The inverse is built from lifted regular
functions and the chart's nonvanishing denominator. -/
theorem exists_affineChartComap_localLeftInverse
    (h : A →ₐ[ℂ] B) (hh : Function.Surjective h)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (he : e ∈ SmoothSchemeManifold.affineRegularAtlas B n) (hf : f ∈ SmoothSchemeManifold.affineRegularAtlas A m)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source)
    (hfx : x.comp h ∈ f.source) :
    ∃ Ψ : (Fin m → ℂ) → (Fin n → ℂ),
      ContDiffAt ℂ ω Ψ (f (x.comp h)) ∧
      (fun z => Ψ (f ((e.symm z).comp h))) =ᶠ[𝓝 (e x)] id := by
  classical
  obtain ⟨g, hg, hcoords⟩ := he.2
  obtain ⟨gA, hgA⟩ := hh g
  choose b k hb using hcoords
  choose a ha using fun i => hh (b i)
  let Ψ : (Fin m → ℂ) → (Fin n → ℂ) :=
    fun w i => f.symm w (a i) / (f.symm w gA) ^ (k i)
  refine ⟨Ψ, ?_, ?_⟩
  · apply contDiffAt_pi.mpr
    intro i
    have htarget : f.target ∈ 𝓝 (f (x.comp h)) :=
      f.open_target.mem_nhds (f.map_source hfx)
    have hnz : f.symm (f (x.comp h)) gA ≠ 0 := by
      rw [f.left_inv hfx]
      change x (h gA) ≠ 0
      rw [hgA]
      exact hg x hx
    exact ((hf.1 (a i)).contDiffAt htarget).div
      (((hf.1 gA).contDiffAt htarget).pow (k i)) (pow_ne_zero _ hnz)
  · filter_upwards [affineChartComap_neighborhood h e f x hx hfx] with z hz
    funext i
    change f.symm (f ((e.symm z).comp h)) (a i) /
      (f.symm (f ((e.symm z).comp h)) gA) ^ (k i) = z i
    rw [f.left_inv hz.2]
    change e.symm z (h (a i)) / (e.symm z (h gA)) ^ (k i) = z i
    rw [ha, hgA, ← hb i (e.symm z) (e.map_target hz.1), e.right_inv hz.1]

/-- The ordinary complex derivative of a genuine affine closed immersion is
injective in any two of the established regular coordinate charts. -/
theorem fderiv_affineChartComap_injective_of_surjective
    (h : A →ₐ[ℂ] B) (hh : Function.Surjective h)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (he : e ∈ SmoothSchemeManifold.affineRegularAtlas B n) (hf : f ∈ SmoothSchemeManifold.affineRegularAtlas A m)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source)
    (hfx : x.comp h ∈ f.source) :
    Function.Injective (fderiv ℂ (fun z => f ((e.symm z).comp h)) (e x)) := by
  obtain ⟨Ψ, hΨ, hleft⟩ := exists_affineChartComap_localLeftInverse h hh e f he hf x hx hfx
  have hΦ := (contDiffAt_affineChartComap h e f he hf x hx hfx).differentiableAt
    (by simp)
  have hΨ' : DifferentiableAt ℂ Ψ (f ((e.symm (e x)).comp h)) := by
    rw [e.left_inv hx]
    exact hΨ.differentiableAt (by simp)
  have hcomp := hleft.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_id] at hcomp
  have hchain := fderiv_comp (e x) hΨ' hΦ
  change fderiv ℂ (fun z => Ψ (f ((e.symm z).comp h))) (e x) = _ at hchain
  rw [hcomp] at hchain
  intro v w hvw
  have hc := congrArg (fderiv ℂ Ψ (f ((e.symm (e x)).comp h))) hvw
  have hv := congrArg (fun L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => L v) hchain
  have hw := congrArg (fun L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => L w) hchain
  exact hv.trans (hc.trans hw.symm)

variable [IsDomain A] [Algebra.Smooth ℂ A] [IsDomain B] [Algebra.Smooth ℂ B]

set_option backward.isDefEq.respectTransparency false in
/-- On the native smooth affine point manifolds, the manifold derivative is
the ordinary derivative in their chosen, proved regular-coordinate charts. -/
theorem mfderiv_smoothDomain_comap_eq_chart_fderiv
    (h : A →ₐ[ℂ] B) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    mfderiv (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ))
        (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ))
        (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) x =
      fderiv ℂ (fun z =>
        chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) (x.comp h)
          (((chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ) x).symm z).comp h))
        (chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ) x x) := by
  rw [((SmoothAffineMaps.contMDiff_smoothDomain_comap h 1).mdifferentiableAt (x := x) one_ne_zero).mfderiv_abuse]
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap, ContinuousMap.coe_mk,
    Function.comp_def, id_eq, Set.range_id, fderivWithin_univ]

/-- A surjection of smooth integral complex coordinate rings induces an
injective complex manifold differential at every actual complex point. -/
theorem mfderiv_smoothDomain_comap_injective_of_surjective
    (h : A →ₐ[ℂ] B) (hh : Function.Surjective h) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    Function.Injective
      (mfderiv (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ))
        (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ))
        (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) x) := by
  rw [mfderiv_smoothDomain_comap_eq_chart_fderiv]
  exact fderiv_affineChartComap_injective_of_surjective h hh
    (chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ) x)
    (chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) (x.comp h))
    (chart_mem_atlas _ x) (chart_mem_atlas _ (x.comp h)) x
    (mem_chart_source _ x) (mem_chart_source _ (x.comp h))

set_option backward.isDefEq.respectTransparency false in
/-- The analogous chart formula for the underlying real smooth manifolds. -/
theorem real_mfderiv_smoothDomain_comap_eq_chart_fderiv
    (h : A →ₐ[ℂ] B) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    mfderiv (𝓘(ℝ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ))
        (𝓘(ℝ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ))
        (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) x =
      fderiv ℝ (fun z =>
        chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) (x.comp h)
          (((chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ) x).symm z).comp h))
        (chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ) x x) := by
  rw [((SmoothAffineMaps.real_contMDiff_smoothDomain_comap h 1).mdifferentiableAt
    (x := x) one_ne_zero).mfderiv_abuse]
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap, ContinuousMap.coe_mk,
    Function.comp_def, id_eq, Set.range_id, fderivWithin_univ]

/-- A genuine affine closed immersion also has injective differential on the
underlying real manifolds. This is restriction of its complex differential. -/
theorem real_mfderiv_smoothDomain_comap_injective_of_surjective
    (h : A →ₐ[ℂ] B) (hh : Function.Surjective h) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    Function.Injective
      (mfderiv (𝓘(ℝ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ))
        (𝓘(ℝ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ))
        (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) x) := by
  rw [real_mfderiv_smoothDomain_comap_eq_chart_fderiv]
  have hd := (contDiffAt_affineChartComap h
    (chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ) x)
    (chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) (x.comp h))
    (chart_mem_atlas _ x) (chart_mem_atlas _ (x.comp h)) x
    (mem_chart_source _ x) (mem_chart_source _ (x.comp h))).differentiableAt (by simp)
  rw [hd.fderiv_restrictScalars ℝ]
  exact fderiv_affineChartComap_injective_of_surjective h hh
    (chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ) x)
    (chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) (x.comp h))
    (chart_mem_atlas _ x) (chart_mem_atlas _ (x.comp h)) x
    (mem_chart_source _ x) (mem_chart_source _ (x.comp h))

/-- Native complex points of a smooth affine closed immersion form a closed
embedded complex submanifold in the differential sense: the induced map is a
closed topological embedding and its complex differential is injective. -/
theorem smoothDomain_comap_closedEmbedding_and_injective_differential
    (h : A →ₐ[ℂ] B) (hh : Function.Surjective h) :
    Topology.IsClosedEmbedding (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) ∧
      ∀ x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B,
        Function.Injective
          (mfderiv (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ))
            (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ))
            (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) x) :=
  ⟨Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosedEmbedding_comap_of_surjective h hh,
    mfderiv_smoothDomain_comap_injective_of_surjective h hh⟩

/-- The real differential version, on the very same ordinary complex-point
topology and the underlying real smooth structure. -/
theorem smoothDomain_comap_closedEmbedding_and_injective_real_differential
    (h : A →ₐ[ℂ] B) (hh : Function.Surjective h) :
    Topology.IsClosedEmbedding (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) ∧
      ∀ x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B,
        Function.Injective
          (mfderiv (𝓘(ℝ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ))
            (𝓘(ℝ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ))
            (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) x) :=
  ⟨Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosedEmbedding_comap_of_surjective h hh,
    real_mfderiv_smoothDomain_comap_injective_of_surjective h hh⟩

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion
