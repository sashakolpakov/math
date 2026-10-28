import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalChartMaps
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexOpenOrientation

/-! # Open Fundamental -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.OpenFundamental.Cycles

noncomputable section

/-!
# Open-inclusion naturality of canonical compact-support classes

The maps used below are the actual maps of complementary pairs induced by
continuous injections. Their compatibility with local restrictions follows
from composition of relative singular homology maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section InjectiveMaps

variable {X Y : TopCat.{0}}

/-- An injective continuous map induces an actual relative homology map
from a support to its image, using the complementary subspaces. -/
def injectiveSupportHomologyMap (f : X ⟶ Y) (hf : Function.Injective f)
    (K : Set X) (n : ℕ) :
    HomologyWithSupports.Cycles.singularHomologyWithSupport X K n ⟶ HomologyWithSupports.Cycles.singularHomologyWithSupport Y (f '' K) n :=
  LocalHomology.Cycles.relativeSingularHomologyMap f ((Set.surjOn_image f K).mapsTo_compl hf) n

/-- Support pushforward and the actual punctured-pair map give the same
class at every point of the image. -/
@[reassoc]
theorem injectiveSupportHomologyMap_toPoint (f : X ⟶ Y) (hf : Function.Injective f)
    (K : Set X) (n : ℕ) (x : X) (hx : x ∈ K) :
    injectiveSupportHomologyMap f hf K n ≫
        LocalHomologyPresheaf.Cycles.localHomologyToPoint Y (f '' K) (f x) ⟨x, hx, rfl⟩ n =
      LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n ≫ LocalChartMaps.Cycles.injectiveLocalHomologyMap f hf x n := by
  unfold injectiveSupportHomologyMap LocalHomologyPresheaf.Cycles.localHomologyToPoint LocalChartMaps.Cycles.injectiveLocalHomologyMap
  change LocalHomology.Cycles.relativeSingularHomologyMap f _ n ≫ LocalHomology.Cycles.relativeSingularHomologyMap (𝟙 Y) _ n =
    LocalHomology.Cycles.relativeSingularHomologyMap (𝟙 X) _ n ≫ LocalHomology.Cycles.relativeSingularHomologyMap f _ n
  rw [LocalHomology.Cycles.relativeSingularHomologyMap_comp, LocalHomology.Cycles.relativeSingularHomologyMap_comp]
  simp only [Category.id_comp, Category.comp_id]

end InjectiveMaps

section LocalCriterion

variable (p : ℕ) {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [T2Space M] [T2Space N]
variable [ChartedSpace (Fin p → ℂ) M] [ChartedSpace (Fin p → ℂ) N]
variable [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 N]

/-- A continuous injection preserving the specified actual local classes
preserves every compact-support fundamental class. This explicit local
criterion will be discharged for the open inclusions below. -/
theorem complexCompactFundamentalClass_map_of_local
    (f : TopCat.of M ⟶ TopCat.of N) (hf : Function.Injective f)
    (hlocal : ∀ x : M, LocalChartMaps.Cycles.injectiveLocalHomologyMap f hf x (2 * p)
      (ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x) = ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) (f x))
    (K : Set M) (hK : IsCompact K) :
    injectiveSupportHomologyMap f hf K (2 * p) (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p K hK) =
      ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (f '' K) (hK.image f.hom.continuous) := by
  apply ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_unique p (f '' K) (hK.image f.hom.continuous)
  rintro y ⟨x, hx, rfl⟩
  have hs := ConcreteCategory.congr_hom
    (injectiveSupportHomologyMap_toPoint f hf K (2 * p) x hx)
    (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p K hK)
  change LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of N) (f '' K) (f x) _ (2 * p)
      (injectiveSupportHomologyMap f hf K (2 * p) (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p K hK)) =
    LocalChartMaps.Cycles.injectiveLocalHomologyMap f hf x (2 * p)
      (LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * p)
        (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p K hK)) at hs
  rw [hs, ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_atPoint]
  exact hlocal x

end LocalCriterion

variable (p : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin p → ℂ) M] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M]

/-- The literal map of complementary pairs induced by an open-subspace
inclusion takes the canonical compact-support class to the image class. -/
theorem complexCompactFundamentalClass_openInclusion
    (U : Opens M) (K : Set U) (hK : IsCompact K) :
    LocalHomology.Cycles.relativeSingularHomologyMap (LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M))
        ((Set.surjOn_image (LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) K).mapsTo_compl
          Subtype.val_injective) (2 * p) (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (M := U) K hK) =
      ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (M := M)
        ((LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) '' K)
        (hK.image (LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)).hom.continuous) := by
  change injectiveSupportHomologyMap (LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M))
      Subtype.val_injective K (2 * p) (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (M := U) K hK) = _
  apply complexCompactFundamentalClass_map_of_local p (M := U) (N := M) _ _ _ K hK
  intro x
  change (LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of M) (U : Set M)
      x.val x.property U.isOpen (2 * p)).hom
        (ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) (M := U) x) =
      ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) (M := M) x.val
  exact ComplexOpenOrientation.Cycles.complexCanonicalLocalClass_open_inclusion (p := p) U x

/-- The compact-support excision isomorphism preserves the canonical
classes for any compact ambient support contained in the open subspace. -/
theorem complexCompactFundamentalClass_openExcision
    (U : Opens M) (K : Set M) (hK : IsCompact K) (hKU : K ⊆ (U : Set M)) :
    (CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso (TopCat.of M) (U : Set M) K hK U.isOpen hKU
        (2 * p)).hom
      (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (M := U)
        ((LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) ⁻¹' K)
        (CompactSupportExcision.Cycles.compactSupport_preimage_isCompact (TopCat.of M) (U : Set M) K hK hKU)) =
      ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (M := M) K hK := by
  apply ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_unique p K hK
  intro x hx
  have hs := ConcreteCategory.congr_hom
    (CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso_toPoint
      (TopCat.of M) (U : Set M) K hK U.isOpen hKU x hx (2 * p))
    (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (M := U)
      ((LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) ⁻¹' K)
      (CompactSupportExcision.Cycles.compactSupport_preimage_isCompact (TopCat.of M) (U : Set M) K hK hKU))
  change LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * p)
      ((CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso (TopCat.of M) (U : Set M) K hK U.isOpen hKU
        (2 * p)).hom _) =
    (LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of M) (U : Set M) x (hKU hx) U.isOpen (2 * p)).hom
      (LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of U)
        ((LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) ⁻¹' K)
        (⟨x, hKU hx⟩ : U) hx (2 * p) _) at hs
  rw [hs, ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_atPoint]
  exact ComplexOpenOrientation.Cycles.complexCanonicalLocalClass_open_inclusion (p := p) U (⟨x, hKU hx⟩ : U)

/-- For nested open sets, the actual punctured-pair inclusion also
preserves their inherited complex local generators. -/
theorem complexCanonicalLocalClass_opensInclusion
    (U V : Opens M) (hUV : U ≤ V) (x : U) :
    LocalChartMaps.Cycles.injectiveLocalHomologyMap
        (TopCat.ofHom (ContinuousMap.inclusion hUV) : TopCat.of U ⟶ TopCat.of V)
        (Set.inclusion_injective hUV) x (2 * p)
        (ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) (M := U) x) =
      ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) (M := V) (Set.inclusion hUV x) := by
  let f : TopCat.of U ⟶ TopCat.of V := TopCat.ofHom (ContinuousMap.inclusion hUV)
  let q := LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of M) (V : Set M)
    x.val (hUV x.property) V.isOpen (2 * p)
  have hcomp : LocalChartMaps.Cycles.injectiveLocalHomologyMap f (Set.inclusion_injective hUV) x (2 * p) ≫
      q.hom =
    (LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of M) (U : Set M)
      x.val x.property U.isOpen (2 * p)).hom := by
    dsimp only [q]
    simp only [LocalExcision.Cycles.localExcisionHomologyIso_hom, LocalChartMaps.Cycles.localExcisionHomologyMap_eq_injective]
    exact LocalChartMaps.Cycles.injectiveLocalHomologyMap_comp f (LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (V : Set M))
      (Set.inclusion_injective hUV) Subtype.val_injective x (2 * p)
  apply q.toLinearEquiv.injective
  change q.hom (LocalChartMaps.Cycles.injectiveLocalHomologyMap f (Set.inclusion_injective hUV) x (2 * p)
      (ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) (M := U) x)) =
    q.hom (ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) (M := V) (Set.inclusion hUV x))
  have hh := ConcreteCategory.congr_hom hcomp (ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) (M := U) x)
  change q.hom (LocalChartMaps.Cycles.injectiveLocalHomologyMap f (Set.inclusion_injective hUV) x (2 * p)
      (ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) (M := U) x)) = _ at hh
  rw [hh]
  exact (ComplexOpenOrientation.Cycles.complexCanonicalLocalClass_open_inclusion (p := p) U x).trans
    (ComplexOpenOrientation.Cycles.complexCanonicalLocalClass_open_inclusion (p := p) V (Set.inclusion hUV x)).symm

/-- The literal relative homology map of an inclusion between nested
open subspaces preserves every canonical compact-support fundamental class. -/
theorem complexCompactFundamentalClass_opensInclusion
    (U V : Opens M) (hUV : U ≤ V) (K : Set U) (hK : IsCompact K) :
    LocalHomology.Cycles.relativeSingularHomologyMap
        (TopCat.ofHom (ContinuousMap.inclusion hUV) : TopCat.of U ⟶ TopCat.of V)
        ((Set.surjOn_image (Set.inclusion hUV) K).mapsTo_compl
          (Set.inclusion_injective hUV)) (2 * p) (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (M := U) K hK) =
      ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (M := V) ((Set.inclusion hUV) '' K)
        (hK.image (continuous_inclusion hUV)) := by
  change injectiveSupportHomologyMap
      (TopCat.ofHom (ContinuousMap.inclusion hUV) : TopCat.of U ⟶ TopCat.of V)
      (Set.inclusion_injective hUV) K (2 * p) (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p (M := U) K hK) = _
  exact complexCompactFundamentalClass_map_of_local p (M := U) (N := V) _ _
    (complexCanonicalLocalClass_opensInclusion p U V hUV) K hK

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.OpenFundamental.Cycles
