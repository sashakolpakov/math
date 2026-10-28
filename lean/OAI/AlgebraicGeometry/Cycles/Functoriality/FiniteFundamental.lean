import OAI.AlgebraicGeometry.CycleClass.Geometric.OpenFundamental
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexFundamentalNaturality

/-! # Finite Fundamental -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.FiniteFundamental.Construction

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

/-- A map into the subspace of a relative pair induces zero on relative
homology, since it factors through the zero relative group of the whole source. -/
theorem relativeHomologyMap_eq_zero_of_range_subset
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hAB : Set.MapsTo f A B) (hB : ∀ x, f x ∈ B) (n : ℕ) :
    CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f hAB n = 0 := by
  have hz : IsZero (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X Set.univ n) := by
    simpa only [CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport, Set.compl_empty] using
      CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupport_empty_isZero X n
  have hcomp := CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_comp (𝟙 X) f
    (A := A) (B := Set.univ) (C := B) (fun _ _ => trivial) (fun x _ => hB x) n
  simp only [Category.id_comp] at hcomp
  rw [← hcomp, hz.eq_of_tgt (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (𝟙 X)
    (A := A) (B := Set.univ) (fun _ _ => trivial) n) 0, zero_comp]

/-- A neighborhood isolating one point of a support gives an actual map
from that local homology group to homology with the entire support. -/
def finiteSupportLocalInsertion
    {M : Type} [TopologicalSpace M] (K : Set M) (U : Opens M)
    (x : U) (hUK : ∀ y : U, y.val ∈ K → y = x) (n : ℕ) :
    CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of U) x n ⟶
      CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K n :=
  CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M))
    (A := ({x} : Set U)ᶜ) (B := Kᶜ) (by
      intro y hy
      change y ≠ x at hy
      change y.val ∉ K
      exact fun hyK => hy (hUK y hyK)) n

/-- At its own point, local insertion restricts to the usual open
inclusion map on local homology. -/
theorem finiteSupportLocalInsertion_to_self
    {M : Type} [TopologicalSpace M] (K : Set M) (U : Opens M)
    (x : U) (hxK : x.val ∈ K) (hUK : ∀ y : U, y.val ∈ K → y = x) (n : ℕ) :
    finiteSupportLocalInsertion K U x hUK n ≫
      CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x.val hxK n =
    CycleClass.Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M))
      Subtype.val_injective x n := by
  have hf : Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M))
      ({x} : Set U)ᶜ Kᶜ := fun y hy hyK => hy (hUK y hyK)
  have hg : Set.MapsTo (𝟙 (TopCat.of M)) Kᶜ ({x.val} : Set M)ᶜ := by
    intro y hy
    change y ≠ x.val
    intro hxy
    exact hy (hxy.symm ▸ hxK)
  have hcomp := CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_comp
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) (𝟙 (TopCat.of M)) hf hg n
  exact hcomp.trans (CycleClass.Geometric.LocalChartMaps.Cycles.relativeSingularHomologyMap_congr (Category.comp_id _) _ _ n)

/-- At every other point of the support, the inserted local class
vanishes because the whole isolating neighborhood avoids that point. -/
theorem finiteSupportLocalInsertion_to_other
    {M : Type} [TopologicalSpace M] (K : Set M) (U : Opens M)
    (x : U) (hUK : ∀ y : U, y.val ∈ K → y = x)
    (z : M) (hzK : z ∈ K) (hzx : z ≠ x.val) (n : ℕ) :
    finiteSupportLocalInsertion K U x hUK n ≫
      CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K z hzK n = 0 := by
  have hf : Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M))
      ({x} : Set U)ᶜ Kᶜ := fun y hy hyK => hy (hUK y hyK)
  have hg : Set.MapsTo (𝟙 (TopCat.of M)) Kᶜ ({z} : Set M)ᶜ := by
    intro y hy
    change y ≠ z
    intro hxy
    exact hy (hxy.symm ▸ hzK)
  have hcomp := CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_comp
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) (𝟙 (TopCat.of M)) hf hg n
  have hzero := relativeHomologyMap_eq_zero_of_range_subset
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M) ≫ 𝟙 (TopCat.of M))
    (fun _ hx => hg (hf hx)) (fun y hyz => ?_) n
  · exact hcomp.trans hzero
  · change y.val = z at hyz
    have hyx := hUK y (hyz.symm ▸ hzK)
    exact hzx (hyz.symm.trans (congrArg Subtype.val hyx))

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin d → ℂ) M] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M]

/-- The local fundamental generator inserted into an isolating
neighborhood has the canonical value at its own support point. -/
theorem finiteSupportLocalInsertion_fundamental_self
    (K : Set M) (U : Opens M) (x : U) (hxK : x.val ∈ K)
    (hUK : ∀ y : U, y.val ∈ K → y = x) :
    CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x.val hxK (2 * d)
      (finiteSupportLocalInsertion K U x hUK (2 * d)
        (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x)) =
      CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x.val := by
  have h := ConcreteCategory.congr_hom
    (finiteSupportLocalInsertion_to_self K U x hxK hUK (2 * d))
    (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x)
  exact h.trans (CycleClass.Geometric.ComplexOpenOrientation.Cycles.complexCanonicalLocalClass_open_inclusion (p := d) U x)

/-- The compact fundamental class at a finite support is the sum of
its canonical local generators, inserted through isolating open neighborhoods. -/
theorem complexCompactFundamentalClass_finite_sum
    (K : Set M) [Fintype K] (U : K → Opens M)
    (hxU : ∀ x : K, x.val ∈ U x)
    (hUK : ∀ (x : K) (y : U x), y.val ∈ K → y.val = x.val) :
    (∑ x : K, finiteSupportLocalInsertion K (U x) ⟨x.val, hxU x⟩
      (fun y hy => Subtype.ext (hUK x y hy)) (2 * d)
      (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U x) ⟨x.val, hxU x⟩)) =
    CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d K (Set.toFinite K).isCompact := by
  classical
  apply CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_unique d K (Set.toFinite K).isCompact
  intro z hzK
  rw [map_sum]
  rw [Finset.sum_eq_single (⟨z, hzK⟩ : K)]
  · exact finiteSupportLocalInsertion_fundamental_self d K (U ⟨z, hzK⟩)
      ⟨z, hxU ⟨z, hzK⟩⟩ hzK _
  · intro x _ hx
    have hzx : z ≠ x.val := fun h => hx (Subtype.ext h.symm)
    exact ConcreteCategory.congr_hom
      (finiteSupportLocalInsertion_to_other K (U x) ⟨x.val, hxU x⟩ _
        z hzK hzx (2 * d))
      (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U x) ⟨x.val, hxU x⟩)
  · simp

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.FiniteFundamental.Construction
