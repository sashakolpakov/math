import OAI.AlgebraicTopology.Cohomology.Singular.Contractible
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality
import OAI.AlgebraicTopology.Cohomology.Singular.ChartLocalContractible
import Mathlib.Topology.Category.TopCat.Opens

/-! # Local Primitives -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.LocalPrimitives

noncomputable section

/-!
# Local primitives for genuine singular cocycles

Positive-degree singular cocycles become coboundaries on sufficiently small
open neighborhoods in a strongly locally contractible space. The contraction
is used on an actual contractible neighborhood; the final open neighborhood
is its interior. Thus no openness hypothesis is silently added to mathlib's
definition of strong local contractibility.

For spaces charted on real normed vector spaces, the local contractibility
hypothesis is discharged by the already proved chart-ball basis.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Topology

variable {R : Type} [Ring R]

/-- A cochain map carries an actual primitive to a primitive of the image.
This uses the verified differentials of the two cochain complexes. -/
theorem cochainMap_primitive
    {K L : CochainComplex (ModuleCat.{0} R) ℕ} (f : K ⟶ L)
    (n : ℕ) (b : K.X n) (c : K.X (n + 1))
    (h : K.d n (n + 1) b = c) :
    L.d n (n + 1) ((f.f n) b) = (f.f (n + 1)) c := by
  simpa only [ConcreteCategory.comp_apply, h] using
    (ConcreteCategory.congr_hom (f.comm n (n + 1)) b)

/-- Every genuine positive-degree singular cocycle is locally a coboundary
on a strongly locally contractible space. -/
theorem exists_local_singularPrimitive (A : ModuleCat.{0} R)
    (X : TopCat.{0}) [StronglyLocallyContractibleSpace X]
    (U : Opens X) (x : X) (hxU : x ∈ U) (n : ℕ)
    (c : Representatives.singularCocycles A (TopCat.of U) (n + 1)) :
    ∃ (V : Opens X) (_hxV : x ∈ V) (hVU : V ≤ U)
      (b : (Basic.singularCochains A (TopCat.of V)).X n),
      (Basic.singularCochains A (TopCat.of V)).d n (n + 1) b =
        ((Functor.singularPullback A ((Opens.toTopCat X).map (homOfLE hVU))).f (n + 1)) c.1 := by
  obtain ⟨W, ⟨hWx, hWc⟩, hWU⟩ :=
    (contractible_basis x).mem_iff.mp (U.isOpen.mem_nhds hxU)
  let V : Opens X := ⟨interior W, isOpen_interior⟩
  have hxV : x ∈ V := mem_interior_iff_mem_nhds.mpr hWx
  have hVU : V ≤ U := fun y hy => hWU (interior_subset hy)
  let iWU : TopCat.of W ⟶ TopCat.of U := TopCat.ofHom
    ⟨fun y => ⟨y.1, hWU y.2⟩, continuous_subtype_val.subtype_mk _⟩
  let iVW : TopCat.of V ⟶ TopCat.of W := TopCat.ofHom
    ⟨fun y => ⟨y.1, interior_subset y.2⟩, continuous_subtype_val.subtype_mk _⟩
  let cW := RepresentativesNaturality.cochainCocycleMap (Functor.singularPullback A iWU) (n + 1) c
  let : ContractibleSpace W := hWc
  obtain ⟨bW, hbW⟩ := Contractible.exists_singularPrimitive_of_contractible A (TopCat.of W) n cW
  refine ⟨V, hxV, hVU, (Functor.singularPullback A iVW).f n bW, ?_⟩
  have hcomp : iVW ≫ iWU = (Opens.toTopCat X).map (homOfLE hVU) := by
    ext y
    rfl
  have hmap := cochainMap_primitive (Functor.singularPullback A iVW) n bW cW.1 hbW
  change (Basic.singularCochains A (TopCat.of V)).d n (n + 1)
      ((Functor.singularPullback A iVW).f n bW) =
    (Functor.singularPullback A iVW).f (n + 1)
      ((Functor.singularPullback A iWU).f (n + 1) c.1) at hmap
  rw [← hcomp]
  change (Basic.singularCochains A (TopCat.of V)).d n (n + 1)
      ((Functor.singularPullback A iVW).f n bW) =
    (Functor.singularPullback A (iVW ≫ iWU)).f (n + 1) c.1
  rw [Functor.singularPullback_comp A iVW iWU]
  exact hmap

/-- The same local primitive theorem for genuine real normed manifold
charts, with no local contractibility assumption supplied by the caller. -/
theorem exists_local_singularPrimitive_of_chartedSpace
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ModuleCat.{0} R) (X : TopCat.{0}) [ChartedSpace E X]
    (U : Opens X) (x : X) (hxU : x ∈ U) (n : ℕ)
    (c : Representatives.singularCocycles A (TopCat.of U) (n + 1)) :
    ∃ (V : Opens X) (_hxV : x ∈ V) (hVU : V ≤ U)
      (b : (Basic.singularCochains A (TopCat.of V)).X n),
      (Basic.singularCochains A (TopCat.of V)).d n (n + 1) b =
        ((Functor.singularPullback A ((Opens.toTopCat X).map (homOfLE hVU))).f (n + 1)) c.1 := by
  let := ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace E X
  exact exists_local_singularPrimitive A X U x hxU n c

end

end OAI.AlgebraicTopology.Cohomology.Singular.LocalPrimitives
