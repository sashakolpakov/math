import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicImmersionNormalPair
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairTransition
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Normal Coordinates Differentiable -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable

noncomputable section

/-!
# Differentiability of the constructed normal coordinates

The normal coordinates constructed from a genuine immersion are compositions
of its maximal-atlas charts with a continuous linear equivalence and a
translation. We prove their regularity directly from those constructions.
No regularity is asserted for an arbitrary topological normal-pair structure.
-/

open scoped ContDiff _root_.Manifold _root_.Topology
open Set

section

section TangentialTranslations

variable {K E G C N : Type*} [NontriviallyNormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup G] [NormedSpace K G]
variable [NormedAddCommGroup C] [NormedSpace K C]
variable [TopologicalSpace N] [ChartedSpace G N]

/-- Translating only the tangential coordinates of an actual differentiable
chart preserves differentiability in both directions. This applies to
recentered normal pairs once the original chart's regularity is proved. -/
theorem mdifferentiable_transHomeomorph_tangentialTranslation
    (c : OpenPartialHomeomorph N (E × C))
    (hc : c.MDifferentiable 𝓘(K, G) 𝓘(K, E × C)) (a : E) :
    (c.transHomeomorph ((Homeomorph.subRight a).prodCongr (Homeomorph.refl C))).MDifferentiable
      𝓘(K, G) 𝓘(K, E × C) := by
  let t : (E × C) ≃ₜ (E × C) :=
    (Homeomorph.subRight a).prodCongr (Homeomorph.refl C)
  have ht : t.toOpenPartialHomeomorph.MDifferentiable 𝓘(K, E × C) 𝓘(K, E × C) := by
    constructor
    · have ht' : ContDiff K 1 (fun z : E × C => (z.1 - a, z.2)) :=
        (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
      exact ht'.contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero
    · have ht' : ContDiff K 1 (fun z : E × C => (z.1 + a, z.2)) :=
        (contDiff_fst.add contDiff_const).prodMk contDiff_snd
      exact ht'.contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero
  rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
  exact hc.trans ht

namespace ImmersionNormalPair

variable {M : Type*} {f : M → N} {x : M}

/-- Recentering transports a proved ambient-chart differentiability
statement; it does not impose regularity on an arbitrary topological pair. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.recenterChart_mdifferentiable (P : NormalPairRecenter.ImmersionNormalPair E C f x)
    (hP : P.ambientChart.MDifferentiable 𝓘(K, G) 𝓘(K, E × C)) (z : M) :
    (P.recenterChart z).MDifferentiable 𝓘(K, G) 𝓘(K, E × C) :=
  mdifferentiable_transHomeomorph_tangentialTranslation P.ambientChart hP
    (P.ambientChart (f z)).1

/-- The full-image normal pair obtained by recentering and shrinking keeps
the proved differentiability of its ambient coordinates and inverse. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.recenterWithin_ambientChart_mdifferentiable (P : NormalPairRecenter.ImmersionNormalPair E C f x)
    (hP : P.ambientChart.MDifferentiable 𝓘(K, G) 𝓘(K, E × C))
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    (P.recenterWithin z hz U hU).ambientChart.MDifferentiable
      𝓘(K, G) 𝓘(K, E × C) :=
  P.recenterChart_mdifferentiable hP z

end ImmersionNormalPair

end TangentialTranslations

section ConstructedCoordinates

variable {K E G C M N : Type*} [NontriviallyNormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup G] [NormedSpace K G]
variable [NormedAddCommGroup C] [NormedSpace K C]
variable [TopologicalSpace M] [ChartedSpace E M]
variable [TopologicalSpace N] [ChartedSpace G N]
variable {n : ℕ∞ω} {f : M → N} {x : M}

/-- Centering the immersion's source chart preserves its differentiability
order on the actual source. -/
theorem contMDiffOn_immersionSourceCoordinates
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x) :
    ContMDiffOn 𝓘(K, E) 𝓘(K, E) n (NormalPairRecenter.immersionSourceCoordinates h)
      (NormalPairRecenter.immersionSourceCoordinates h).source := by
  have ht : ContDiff K n (fun z : E => z - h.domChart x) :=
    contDiff_id.sub contDiff_const
  exact ht.contMDiff.comp_contMDiffOn
    (contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas)

/-- The inverse centered source chart has the same differentiability order. -/
theorem contMDiffOn_immersionSourceCoordinates_symm
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x) :
    ContMDiffOn 𝓘(K, E) 𝓘(K, E) n (NormalPairRecenter.immersionSourceCoordinates h).symm
      (NormalPairRecenter.immersionSourceCoordinates h).target := by
  have ht : ContDiff K n (fun z : E => z + h.domChart x) :=
    contDiff_id.add contDiff_const
  exact (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).comp
    ht.contMDiff.contMDiffOn (fun _ hz => hz)

/-- The actual split and centered ambient chart is as differentiable as
the genuine immersion chart from which it was constructed. -/
theorem contMDiffOn_immersionNormalCoordinates
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x) :
    ContMDiffOn 𝓘(K, G) 𝓘(K, E × C) n (NormalPairRecenter.immersionNormalCoordinates h)
      (NormalPairRecenter.immersionNormalCoordinates h).source := by
  have ht : ContDiff K n (fun z : G =>
      ((h.equiv.symm z).1 - h.domChart x, (h.equiv.symm z).2)) :=
    (h.equiv.symm.contDiff.fst.sub contDiff_const).prodMk h.equiv.symm.contDiff.snd
  exact ht.contMDiff.comp_contMDiffOn
    (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas)

/-- Its actual inverse is also differentiable on the complete chart target. -/
theorem contMDiffOn_immersionNormalCoordinates_symm
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x) :
    ContMDiffOn 𝓘(K, E × C) 𝓘(K, G) n (NormalPairRecenter.immersionNormalCoordinates h).symm
      (NormalPairRecenter.immersionNormalCoordinates h).target := by
  have ht : ContDiff K n (fun z : E × C => h.equiv (z.1 + h.domChart x, z.2)) :=
    h.equiv.contDiff.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
  exact (contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
    ht.contMDiff.contMDiffOn (fun _ hz => hz)

/-- A positive-order source chart is a genuine differentiable local
homeomorphism, with differentiable inverse. -/
theorem immersionSourceCoordinates_mdifferentiable
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x)
    (hn : n ≠ 0) :
    (NormalPairRecenter.immersionSourceCoordinates h).MDifferentiable 𝓘(K, E) 𝓘(K, E) :=
  ⟨(contMDiffOn_immersionSourceCoordinates h).mdifferentiableOn hn,
    (contMDiffOn_immersionSourceCoordinates_symm h).mdifferentiableOn hn⟩

/-- Positive-order normal coordinates are genuine differentiable local
homeomorphisms in both directions. -/
theorem immersionNormalCoordinates_mdifferentiable
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x)
    (hn : n ≠ 0) :
    (NormalPairRecenter.immersionNormalCoordinates h).MDifferentiable 𝓘(K, G) 𝓘(K, E × C) :=
  ⟨(contMDiffOn_immersionNormalCoordinates h).mdifferentiableOn hn,
    (contMDiffOn_immersionNormalCoordinates_symm h).mdifferentiableOn hn⟩

/-- The ambient chart of the actual full-image normal pair inherits the
proved differentiability; the embedding only selects its radius. -/
theorem normalPairOfImmersion_ambientChart_mdifferentiable
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x)
    (hf : Topology.IsEmbedding f) (hn : n ≠ 0) :
    (NormalPairRecenter.normalPairOfImmersion h hf).ambientChart.MDifferentiable
      𝓘(K, G) 𝓘(K, E × C) :=
  immersionNormalCoordinates_mdifferentiable h hn

/-- The same statement for the actual complement chosen by `IsImmersionAt`. -/
theorem immersionNormalPair_ambientChart_mdifferentiable
    (h : Manifold.IsImmersionAt 𝓘(K, E) 𝓘(K, G) n f x)
    (hf : Topology.IsEmbedding f) (hn : n ≠ 0) :
    (NormalPairRecenter.immersionNormalPair h hf).ambientChart.MDifferentiable
      𝓘(K, G) 𝓘(K, E × h.complement) :=
  normalPairOfImmersion_ambientChart_mdifferentiable
    h.isImmersionAtOfComplement_complement hf hn

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace K D] {m : ℕ∞ω}

/-- The transition on the verified overlap of two actual immersion normal
pairs is differentiable with a differentiable inverse. The two normal
coordinate models may be different. -/
theorem normalPairOfImmersion_transition_mdifferentiable
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x)
    (k : Manifold.IsImmersionAtOfComplement D 𝓘(K, E) 𝓘(K, G) m f x)
    (hf : Topology.IsEmbedding f) (hn : n ≠ 0) (hm : m ≠ 0) :
    ((NormalPairRecenter.normalPairOfImmersion h hf).transition (NormalPairRecenter.normalPairOfImmersion k hf)).MDifferentiable
      𝓘(K, E × C) 𝓘(K, E × D) :=
  NormalPairRecenter.ImmersionNormalPair.transition_mdifferentiable
    (NormalPairRecenter.normalPairOfImmersion h hf) (NormalPairRecenter.normalPairOfImmersion k hf)
    (normalPairOfImmersion_ambientChart_mdifferentiable h hf hn)
    (normalPairOfImmersion_ambientChart_mdifferentiable k hf hm)

set_option backward.isDefEq.respectTransparency false in
/-- Invertibility of the actual transition derivative follows from the
proved differentiability of the actual inverse, with no chosen linear map. -/
theorem normalPairOfImmersion_transition_fderiv_bijective
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x)
    (k : Manifold.IsImmersionAtOfComplement D 𝓘(K, E) 𝓘(K, G) m f x)
    (hf : Topology.IsEmbedding f) (hn : n ≠ 0) (hm : m ≠ 0) :
    Function.Bijective
      (fderiv K ((NormalPairRecenter.normalPairOfImmersion h hf).transition (NormalPairRecenter.normalPairOfImmersion k hf))
        (0, 0)) := by
  have hd := normalPairOfImmersion_transition_mdifferentiable h k hf hn hm
  let L : (E × C) ≃L[K] (E × D) := hd.mfderiv
    ((NormalPairRecenter.normalPairOfImmersion h hf).zero_mem_transition_source (NormalPairRecenter.normalPairOfImmersion k hf))
  have hL : L.toContinuousLinearMap =
      fderiv K ((NormalPairRecenter.normalPairOfImmersion h hf).transition (NormalPairRecenter.normalPairOfImmersion k hf))
        (0, 0) := mfderiv_eq_fderiv
  have hb : Function.Bijective L.toContinuousLinearMap := L.bijective
  rwa [hL] at hb

/-- At an arbitrary shared image point of two genuine normal pairs,
recentering inside the overlap gives a differentiable coordinate transition
with differentiable inverse. All chart regularity comes from the immersion. -/
theorem normalPairOfImmersion_recentered_transition_mdifferentiable
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(K, E) 𝓘(K, G) n f x)
    {y : M} (k : Manifold.IsImmersionAtOfComplement D 𝓘(K, E) 𝓘(K, G) m f y)
    (hf : Topology.IsEmbedding f) (hn : n ≠ 0) (hm : m ≠ 0)
    (z : M) (hz : f z ∈ (NormalPairRecenter.normalPairOfImmersion h hf).neighborhood)
    (hz' : f z ∈ (NormalPairRecenter.normalPairOfImmersion k hf).neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    (((NormalPairRecenter.normalPairOfImmersion h hf).recenterWithin z hz U hU).transition
      ((NormalPairRecenter.normalPairOfImmersion k hf).recenterWithin z hz' U hU)).MDifferentiable
      𝓘(K, E × C) 𝓘(K, E × D) :=
  NormalPairRecenter.ImmersionNormalPair.transition_mdifferentiable _ _
    ((NormalPairRecenter.normalPairOfImmersion h hf).recenterWithin_ambientChart_mdifferentiable
      (normalPairOfImmersion_ambientChart_mdifferentiable h hf hn) z hz U hU)
    ((NormalPairRecenter.normalPairOfImmersion k hf).recenterWithin_ambientChart_mdifferentiable
      (normalPairOfImmersion_ambientChart_mdifferentiable k hf hm) z hz' U hU)

end ConstructedCoordinates

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)

/-- The native scheme immersion's actual normal pair has a complex
differentiable ambient chart and inverse, with no regularity hypothesis left. -/
theorem nativeSchemeNormalPair_ambientChart_mdifferentiable
    (φ : X ⟶ Y) [AlgebraicGeometry.IsImmersion φ.left] (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    (IntrinsicImmersionNormalPair.nativeSchemeNormalPair φ x).ambientChart.MDifferentiable
      𝓘(ℂ, ModelY) 𝓘(ℂ, ModelX × IntrinsicImmersionNormalPair.NativeSchemeChartComplement φ x) :=
  immersionNormalPair_ambientChart_mdifferentiable (ImmersionNormalForm.nativeScheme_isImmersionAt φ x)
    (SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion φ) (by simp)

end

namespace DimensionCycleSupport

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The regular support's actual normal pair is a genuine complex
differentiable chart of the boundary-complement ambient manifold. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementNormalPair_ambientChart_mdifferentiable
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (x : Z.regularAnalyticSpace) :
    (Z.regularComplementNormalPair x).ambientChart.MDifferentiable
      𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × Z.RegularComplementChartComplement x) :=
  immersionNormalPair_ambientChart_mdifferentiable
    (Z.regularComplement_isImmersionAt x)
    Z.isClosedEmbedding_regularComplementInclusion.isEmbedding (by simp)

end DimensionCycleSupport

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable
