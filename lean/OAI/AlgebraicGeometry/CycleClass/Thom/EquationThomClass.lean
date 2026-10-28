import OAI.AlgebraicGeometry.CycleClass.Thom.EquationNormalPair
import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OAI.AlgebraicGeometry.CycleClass.Thom.Degree
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport

/-! # Equation Thom Class -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.EquationThomClass.Constructions.RawManifoldCoordinates

/-! Actual submersion equations give normal pairs in arbitrary finite-dimensional complex ambient models, including the graph product model. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N E G : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [ChartedSpace G N] [IsManifold 𝓘(ℂ, G) ω N]

theorem exists_equation_normalPair (u : M → N) (p : ℕ)
    (hdim : Module.finrank ℂ E + p = Module.finrank ℂ G)
    (f : N → (Fin p → ℂ)) (x : M)
    (hf : ContMDiffAt 𝓘(ℂ, G) 𝓘(ℂ, Fin p → ℂ) ω f (u x))
    (hs : Function.Surjective (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, Fin p → ℂ) f (u x)))
    (U : Opens N) (hxU : u x ∈ U) (hzero : ∀ y ∈ U, y ∈ Set.range u ↔ f y = 0) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) u x,
      P.neighborhood ⊆ U ∧ P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)) ∧
      ∀ y : P.neighborhood, P.normalCoordinate y = f y.val := by
  let c := chartAt G (u x)
  let g : G → (Fin p → ℂ) := fun t => f (c.symm t)
  have hgf : ContDiffAt ℂ ω g (c (u x)) := ComplexPoints.Analytic.ImmersionChartDerivative.contDiffAt_preferredChartMap hf
  have hd := ComplexPoints.Analytic.ImmersionChartDerivative.mfderiv_eq_preferredChartDerivative (hf.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℂ, G) 𝓘(ℂ, Fin p → ℂ) f (u x) = fderiv ℂ g (c (u x)) at hd
  have hgs : Function.Surjective (fderiv ℂ g (c (u x))) :=
    (congrArg (fun L : G →L[ℂ] (Fin p → ℂ) => Function.Surjective L) hd).mp hs
  have hk := (fderiv ℂ g (c (u x))).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hgs, finrank_top, Module.finrank_fin_fun] at hk
  have he : Module.finrank ℂ (fderiv ℂ g (c (u x))).ker = Module.finrank ℂ E := by omega
  have hx : u x ∈ c.source ∩ (U : Set N) := ⟨mem_chart_source _ _, hxU⟩
  have hz : ∀ y ∈ c.source ∩ (U : Set N), y ∈ Set.range u ↔ g (c y) = 0 := by
    intro y hy
    change _ ↔ f (c.symm (c y)) = 0
    rw [c.left_inv hy.1]
    exact hzero y hy.2
  obtain ⟨P, hPU, hPd, hPn⟩ := EquationNormalPair.Constructions.exists_equation_normalPair u x c
    (mdifferentiable_chart _) (c.source ∩ (U : Set N)) (c.open_source.inter U.isOpen) hx
    Set.inter_subset_left g hgf hgs hz (ContinuousLinearEquiv.ofFinrankEq he)
  refine ⟨P, fun _ hy => (hPU hy).2, hPd, ?_⟩
  intro y
  rw [hPn]
  change f (c.symm (c y.val)) = f y.val
  rw [c.left_inv (hPU y.property).1]

end AlgebraicGeometry.CycleClass.Thom.EquationThomClass.Constructions.RawManifoldCoordinates

namespace AlgebraicGeometry.CycleClass.Thom.EquationThomClass.Constructions.Raw

/-! In an arbitrary finite-dimensional complex ambient model, an actual submersion equation defining a closed immersion pulls back the canonical normal class to its actual Thom class. -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.EquationThomClass.Constructions.RawManifoldCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N E G : Type} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℝ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [ChartedSpace G N] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N]

theorem equation_pullback_eq_Thom (u : M → N) (hu : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω u)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) u x)) (hc : Topology.IsClosedEmbedding u)
    (p : ℕ) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G = p)
    (hdim : Module.finrank ℂ E + p = Module.finrank ℂ G)
    (f : TopCat.of N ⟶ TopCat.of (Fin p → ℂ))
    (hzero : ∀ y, y ∈ Set.range u ↔ f y = 0)
    (hf : ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, Fin p → ℂ) ω f)
    (hs : ∀ x, Function.Surjective (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, Fin p → ℂ) f (u x))) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
      (A := (Set.range u)ᶜ) (B := ({0}ᶜ)) (fun y hy hz => hy ((hzero y).mpr hz))
      (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p) = Degree.Constructions.ThomClass.complexThomClassInDegree u hu hi hc p hp := by
  classical
  choose P _ hPd hPn using (fun x : M => RawManifoldCoordinates.exists_equation_normalPair u p hdim f x (hf (u x)) (hs x)
    ⊤ (Set.mem_univ _) (fun y _ => hzero y))
  apply Degree.Constructions.ThomClass.complexThomClassInDegree_unique u hu hi hc p hp P hPd
  intro x
  rw [(P x).rationalClassFin_eq_normalPullback]
  let j := Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (P x).neighborhood
  have hm : j ≫ f = (P x).normalCoordinate := by
    ext y k
    exact congrFun (hPn x y).symm k
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) j f
      (A := (P x).relativeComplement) (B := (Set.range u)ᶜ) (C := ({0}ᶜ))
      (fun _ hy => hy) (fun y hy hz => hy ((hzero y).mpr hz)) (2 * p)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  apply h.trans
  have hh : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (j ≫ f)
      (A := (P x).relativeComplement) (B := ({0}ᶜ))
      (fun y hy hz => hy ((hzero y.val).mpr hz)) (2 * p) =
        (P x).normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * p) := by
    unfold ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap
    congr 1
  exact ConcreteCategory.congr_hom hh (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)

end AlgebraicGeometry.CycleClass.Thom.EquationThomClass.Constructions.Raw

end

end OAI
