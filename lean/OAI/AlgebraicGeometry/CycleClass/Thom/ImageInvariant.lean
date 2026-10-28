import OAI.AlgebraicGeometry.CycleClass.Thom.EquationThomClass
import OAI.AlgebraicGeometry.CycleClass.Thom.OpenRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.Differential
import OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup
import OAI.AlgebraicGeometry.CycleClass.Thom.FixedNormalPair

/-! # Image Invariant -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.ImageInvariant.Constructions.RawThomNormal

/-! In arbitrary complex ambient models, the actual Thom class of an equal-image immersion has the canonical normal restriction of the original immersion. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.OpenImmersion.Constructions.Raw OAI.AlgebraicGeometry.CycleClass.Thom.OpenRestriction.Constructions.RawThom
open OAI.AlgebraicGeometry.CycleClass.Thom.EquationThomClass.Constructions.Raw OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.Differential.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M L N E W G : Type} [TopologicalSpace L] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] [NormedSpace ℝ W]
  [ChartedSpace W L] [IsManifold 𝓘(ℂ, W) ω L]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [ChartedSpace G N] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N]
  (f : M → N) (g : L → N) (hg : ContMDiff 𝓘(ℂ, W) 𝓘(ℂ, G) ω g)
  (h : Set.range g = Set.range f) {p : ℕ} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)

local instance : ChartedSpace G P.neighborhood := inferInstanceAs (ChartedSpace G P.openNeighborhood)
local instance : MetrizableSpace P.neighborhood := P.openNeighborhood.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance : MetrizableSpace P.openNeighborhood := P.openNeighborhood.isOpenEmbedding'.isEmbedding.metrizableSpace

omit [NormedSpace ℂ E] [NormedSpace ℝ E] [FiniteDimensional ℂ W] [NormedSpace ℝ W]
  [IsManifold 𝓘(ℂ, W) ω L] [FiniteDimensional ℂ G] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N] in
include h in
theorem restrictedRange_normal : Set.range (GraphOpenImmersion.Constructions.restrictedBase g hg P.openNeighborhood) =
    (Subtype.val : P.neighborhood → N) ⁻¹' Set.range f := by
  change Set.range ((P.openNeighborhood : Set N).restrictPreimage g) = _
  rw [Set.range_restrictPreimage, h]
  rfl

omit [TopologicalSpace L] [NormedSpace ℂ E] [NormedSpace ℝ E] [MetrizableSpace N] in
include h in
theorem normal_mapsTo : Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood)
    P.relativeComplement (Set.range g)ᶜ := by
  intro y hy
  rwa [h]

include h in
theorem ThomClass_normal_of_image
    (hgi : ∀ y, Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G) g y)) (hgc : Topology.IsClosedEmbedding g)
    (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension W G = p) (hdim : Module.finrank ℂ W + p = Module.finrank ℂ G)
    (hPd : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)))
    (hPa : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)) ω P.ambientChart P.ambientChart.source) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood)
      (normal_mapsTo f g h P) (2 * p) (Degree.Constructions.ThomClass.complexThomClassInDegree g hg hgi hgc p hp) = P.rationalClassFin := by
  let J := GraphOpenImmersion.Constructions.restrictedBase g hg P.openNeighborhood
  have hzero (y : P.neighborhood) : y ∈ Set.range J ↔ P.normalCoordinate y = 0 := by
    rw [restrictedRange_normal f g hg h P]
    exact P.mem_range_iff y
  have hr : (Set.range J)ᶜ = P.relativeComplement := by
    rw [restrictedRange_normal f g hg h P]
    rfl
  have ho := OpenRestriction.Constructions.RawThom.ThomClass_open_restriction g hg hgi hgc P.openNeighborhood p hp
  have heq := EquationThomClass.Constructions.Raw.equation_pullback_eq_Thom J (GraphOpenImmersion.Constructions.restrictedBase_analytic g hg P.openNeighborhood)
    (OpenImmersion.Constructions.Raw.restrictedBase_differential_injective g hg P.openNeighborhood hgi)
    (OpenImmersion.Constructions.Raw.restrictedBase_closedEmbedding g hg P.openNeighborhood hgc) p hp hdim P.normalCoordinate hzero
    (NormalPair.Differential.Constructions.normalCoordinate_analytic (G := G) P hPa) (fun y => NormalPair.Differential.Constructions.normalCoordinate_submersion (G := G) P hPd (J y))
  have hs := ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood) hr
    (OpenImmersion.Constructions.Raw.restriction_mapsTo g hg P.openNeighborhood) (normal_mapsTo f g h P) (2 * p)
    (Degree.Constructions.ThomClass.complexThomClassInDegree g hg hgi hgc p hp)
  have ht := ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast P.normalCoordinate (B := ({0}ᶜ : Set (Fin p → ℂ))) hr
    (fun y hy hz => hy ((hzero y).mpr hz)) P.normalCoordinate_mapsTo (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  exact hs.symm.trans ((congrArg (fun a => eqToHom (congrArg
    (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) A (2 * p)) hr) a)
    (ho.trans heq.symm)).trans (ht.trans P.rationalClassFin_eq_normalPullback.symm))

end AlgebraicGeometry.CycleClass.Thom.ImageInvariant.Constructions.RawThomNormal

namespace AlgebraicGeometry.CycleClass.Thom.ImageInvariant.Constructions.RawThom

/-! Equal actual closed holomorphic images have equal canonical Thom classes in arbitrary finite-dimensional complex ambient models. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.ImageInvariant.Constructions.RawThomNormal OAI.AlgebraicGeometry.CycleClass.Thom.FixedNormalPair.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem imageMapsTo {M L N : Type} [TopologicalSpace N] (f : M → N) (g : L → N)
    (h : Set.range g = Set.range f) : Set.MapsTo (𝟙 (TopCat.of N)) (Set.range f)ᶜ (Set.range g)ᶜ := by
  intro x hx
  rwa [h]

variable {M L N E W G : Type} [TopologicalSpace M] [TopologicalSpace L] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℝ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] [NormedSpace ℝ W]
  [ChartedSpace W L] [IsManifold 𝓘(ℂ, W) ω L]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [ChartedSpace G N] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N]

theorem ThomClass_eq_of_image (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω f)
    (hfi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) f x)) (hfc : Topology.IsClosedEmbedding f)
    (g : L → N) (hg : ContMDiff 𝓘(ℂ, W) 𝓘(ℂ, G) ω g)
    (hgi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G) g x)) (hgc : Topology.IsClosedEmbedding g)
    (p : ℕ) (hfp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G = p) (hgp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension W G = p)
    (hdim : Module.finrank ℂ W + p = Module.finrank ℂ G) (h : Set.range g = Set.range f) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of N)) (imageMapsTo f g h) (2 * p)
      (Degree.Constructions.ThomClass.complexThomClassInDegree g hg hgi hgc p hgp) = Degree.Constructions.ThomClass.complexThomClassInDegree f hf hfi hfc p hfp := by
  classical
  choose P hPd hPa _ using (fun x : M => FixedNormalPair.Constructions.exists_analytic_normalPair f hf hfi hfc.isEmbedding p hfp x)
  apply Degree.Constructions.ThomClass.complexThomClassInDegree_unique f hf hfi hfc p hfp P hPd
  intro x
  let j := Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (P x).neighborhood
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) j (𝟙 (TopCat.of N))
      (A := (P x).relativeComplement) (B := (Set.range f)ᶜ) (C := (Set.range g)ᶜ)
      (fun _ hy => hy) (imageMapsTo f g h) (2 * p)) (Degree.Constructions.ThomClass.complexThomClassInDegree g hg hgi hgc p hgp)
  have h₂ := ConcreteCategory.congr_hom
    (ThomOpenRestriction.Constructions.pairMap_congr (Category.comp_id j)
      (fun y hy => imageMapsTo f g h hy) (RawThomNormal.normal_mapsTo f g h (P x)) (2 * p))
    (Degree.Constructions.ThomClass.complexThomClassInDegree g hg hgi hgc p hgp)
  exact h₁.trans (h₂.trans (RawThomNormal.ThomClass_normal_of_image f g hg h (P x) hgi hgc hgp hdim (hPd x) (hPa x)))

end AlgebraicGeometry.CycleClass.Thom.ImageInvariant.Constructions.RawThom

end

end OAI
