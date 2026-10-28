import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf
import OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteChainSeparation
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Local Homology Stalk -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyStalk.Cycles

noncomputable section

/-!
# The local-homology presheaf has the intended stalks

For a Hausdorff space, a finite chain supported away from a point is supported
away from an open neighborhood of that point. This elementary compactness
fact lets actual relative cycles and bounding chains descend to sufficiently
small neighborhoods. It proves that the canonical stalk comparison for
`U ↦ H_n(X, X ∖ U; ℤ)` is an isomorphism with `H_n(X, X ∖ {x}; ℤ)`.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0})

/-- Every actual relative chain has an ordinary finite-chain representative. -/
theorem relativeChainProjection_degree_surjective (A : Set X) (n : ℕ) :
    Function.Surjective ((LocalHomology.Cycles.relativeChainProjection X A).f n) :=
  (ModuleCat.epi_iff_surjective _).1
    (LocalHomology.Cycles.relativeChainSequence_degreewiseShortExact X A n).epi_g

private theorem projection_d (A : Set X) (i j : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X i) :
    (LocalHomology.Cycles.relativeChainProjection X A).f j ((LocalHomology.Cycles.integralSingularChains X).d i j c) =
      (LocalHomology.Cycles.relativeSingularChains X A).d i j ((LocalHomology.Cycles.relativeChainProjection X A).f i c) :=
  (ConcreteCategory.congr_hom ((LocalHomology.Cycles.relativeChainProjection X A).comm i j) c).symm

private theorem pointMap_projection_apply (U : Set X) (x : X) (hx : x ∈ U)
    (n : ℕ) (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    (LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint X U x hx).f n
        ((LocalHomology.Cycles.relativeChainProjection X Uᶜ).f n c) =
      (LocalHomology.Cycles.relativeChainProjection X ({x}ᶜ : Set X)).f n c :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint_projection X U x hx) n) c

private theorem restriction_projection_apply {U V : Set X} (hUV : U ⊆ V)
    (n : ℕ) (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hUV).f n
        ((LocalHomology.Cycles.relativeChainProjection X Vᶜ).f n c) =
      (LocalHomology.Cycles.relativeChainProjection X Uᶜ).f n c :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction_projection X hUV) n) c

variable [T2Space X]

/-- Every local relative homology class is represented over an actual open
neighborhood, by shrinking away from the finite boundary support. -/
theorem localHomologyStalkToPoint_surjective (x : X) (n : ℕ) :
    Function.Surjective (LocalHomologyPresheaf.Cycles.localHomologyStalkToPoint X x n) := by
  intro y
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (LocalHomology.Cycles.relativeSingularChains X ({x}ᶜ : Set X)) n y
  obtain ⟨c, hc⟩ := relativeChainProjection_degree_surjective X ({x}ᶜ : Set X) n
    (z : (LocalHomology.Cycles.relativeSingularChains X ({x}ᶜ : Set X)).X n)
  let j := (ComplexShape.down ℕ).next n
  have hdc : (LocalHomology.Cycles.relativeChainProjection X ({x}ᶜ : Set X)).f j
      ((LocalHomology.Cycles.integralSingularChains X).d n j c) = 0 := by
    rw [projection_d, hc]
    exact AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero _ n j z
  obtain ⟨U, hxU, hU⟩ := FiniteChainSeparation.Cycles.exists_open_relative_projection_eq_zero X x j
    ((LocalHomology.Cycles.integralSingularChains X).d n j c) hdc
  have hcycle : (LocalHomology.Cycles.relativeChainProjection X (U : Set X)ᶜ).f n c ∈
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ) n := by
    change (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ).d n j
      ((LocalHomology.Cycles.relativeChainProjection X (U : Set X)ᶜ).f n c) = 0
    rw [← projection_d]
    exact hU
  let zU : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ) n := ⟨_, hcycle⟩
  have hzU : AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint X (U : Set X) x hxU) n zU = z :=
    Subtype.ext ((pointMap_projection_apply X (U : Set X) x hxU n c).trans hc)
  refine ⟨(LocalHomologyPresheaf.Cycles.localHomologyPresheaf X n).germ U x hxU
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ) n zU), ?_⟩
  calc
    (LocalHomologyPresheaf.Cycles.localHomologyStalkToPoint X x n)
        ((LocalHomologyPresheaf.Cycles.localHomologyPresheaf X n).germ U x hxU
          (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ) n zU)) =
        LocalHomologyPresheaf.Cycles.localHomologyToPoint X (U : Set X) x hxU n
          (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ) n zU) :=
      ConcreteCategory.congr_hom (LocalHomologyPresheaf.Cycles.localHomologyStalkToPoint_germ X x n U hxU) _
    _ = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.relativeSingularChains X ({x}ᶜ : Set X)) n
        (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint X (U : Set X) x hxU) n zU) :=
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality _ n zU
    _ = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.relativeSingularChains X ({x}ᶜ : Set X)) n z := by rw [hzU]

/-- A class becoming zero at the point becomes zero on a smaller neighborhood:
lift a bounding chain and shrink away from its finite relative error. -/
theorem localHomologyStalkToPoint_injective (x : X) (n : ℕ) :
    Function.Injective (LocalHomologyPresheaf.Cycles.localHomologyStalkToPoint X x n) := by
  change Function.Injective (LocalHomologyPresheaf.Cycles.localHomologyStalkToPoint X x n).hom
  apply (injective_iff_map_eq_zero (LocalHomologyPresheaf.Cycles.localHomologyStalkToPoint X x n).hom).2
  intro y hy
  obtain ⟨U, hxU, a, rfl⟩ := (LocalHomologyPresheaf.Cycles.localHomologyPresheaf X n).exists_germ_eq y
  have ha : LocalHomologyPresheaf.Cycles.localHomologyToPoint X (U : Set X) x hxU n a = 0 :=
    (ConcreteCategory.congr_hom (LocalHomologyPresheaf.Cycles.localHomologyStalkToPoint_germ X x n U hxU) a).symm.trans hy
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ) n a
  change (HomologicalComplex.homologyMap
    (LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint X (U : Set X) x hxU) n)
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ) n z) = 0 at ha
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality] at ha
  obtain ⟨b, hb⟩ := (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists
    (LocalHomology.Cycles.relativeSingularChains X ({x}ᶜ : Set X)) n _).1 ha
  change (LocalHomology.Cycles.relativeSingularChains X ({x}ᶜ : Set X)).d (n + 1) n b =
    (LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint X (U : Set X) x hxU).f n
      (z : (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ).X n) at hb
  obtain ⟨c, hc⟩ := relativeChainProjection_degree_surjective X (U : Set X)ᶜ n
    (z : (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ).X n)
  obtain ⟨b', hb'⟩ := relativeChainProjection_degree_surjective X ({x}ᶜ : Set X) (n + 1) b
  let e := (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n b' - c
  have hcpoint : (LocalHomology.Cycles.relativeChainProjection X ({x}ᶜ : Set X)).f n c =
      (LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint X (U : Set X) x hxU).f n
        (z : (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ).X n) := by
    rw [← pointMap_projection_apply X (U : Set X) x hxU n c, hc]
  have he : (LocalHomology.Cycles.relativeChainProjection X ({x}ᶜ : Set X)).f n e = 0 := by
    change (LocalHomology.Cycles.relativeChainProjection X ({x}ᶜ : Set X)).f n
      ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n b' - c) = 0
    rw [map_sub, projection_d, hb', hb, hcpoint, sub_self]
  obtain ⟨V, hxV, hVU, hV⟩ :=
    FiniteChainSeparation.Cycles.exists_open_relative_projection_eq_zero_within X x n e he U hxU
  let r := LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X (show (V : Set X) ⊆ (U : Set X) from hVU)
  have heq : (LocalHomology.Cycles.relativeChainProjection X (V : Set X)ᶜ).f n
        ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n b') =
      (LocalHomology.Cycles.relativeChainProjection X (V : Set X)ᶜ).f n c := by
    apply sub_eq_zero.mp
    simpa only [e, map_sub] using hV
  have hbound : (LocalHomology.Cycles.relativeSingularChains X (V : Set X)ᶜ).d (n + 1) n
      ((LocalHomology.Cycles.relativeChainProjection X (V : Set X)ᶜ).f (n + 1) b') =
        r.f n (z : (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ).X n) := by
    calc
      _ = (LocalHomology.Cycles.relativeChainProjection X (V : Set X)ᶜ).f n
          ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n b') := (projection_d X _ _ _ _).symm
      _ = (LocalHomology.Cycles.relativeChainProjection X (V : Set X)ᶜ).f n c := heq
      _ = r.f n ((LocalHomology.Cycles.relativeChainProjection X (U : Set X)ᶜ).f n c) :=
        (restriction_projection_apply X hVU n c).symm
      _ = r.f n (z : (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ).X n) := by rw [hc]
  have hzV : (HomologicalComplex.homologyMap r n)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ) n z) = 0 := by
    rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
    exact (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists _ n _).2
      ⟨(LocalHomology.Cycles.relativeChainProjection X (V : Set X)ᶜ).f (n + 1) b', hbound⟩
  have hgerm := (LocalHomologyPresheaf.Cycles.localHomologyPresheaf X n).germ_res_apply
    (homOfLE hVU) x hxV (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ) n z)
  change (LocalHomologyPresheaf.Cycles.localHomologyPresheaf X n).germ V x hxV
      ((HomologicalComplex.homologyMap r n)
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ) n z)) =
    (LocalHomologyPresheaf.Cycles.localHomologyPresheaf X n).germ U x hxU
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.relativeSingularChains X (U : Set X)ᶜ) n z) at hgerm
  rw [hzV, map_zero] at hgerm
  exact hgerm.symm

/-- The canonical stalk comparison is an isomorphism for Hausdorff spaces. -/
instance localHomologyStalkToPoint_isIso (x : X) (n : ℕ) :
    IsIso (LocalHomologyPresheaf.Cycles.localHomologyStalkToPoint X x n) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ⟨localHomologyStalkToPoint_injective X x n, localHomologyStalkToPoint_surjective X x n⟩

/-- The actual local-homology presheaf has the expected local relative groups as stalks. -/
def localHomologyStalkIso (x : X) (n : ℕ) :
    (LocalHomologyPresheaf.Cycles.localHomologyPresheaf X n).stalk x ≅ LocalHomology.Cycles.localSingularHomology X x n :=
  asIso (LocalHomologyPresheaf.Cycles.localHomologyStalkToPoint X x n)

@[simp]
theorem localHomologyStalkIso_hom (x : X) (n : ℕ) :
    (localHomologyStalkIso X x n).hom = LocalHomologyPresheaf.Cycles.localHomologyStalkToPoint X x n := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyStalk.Cycles
