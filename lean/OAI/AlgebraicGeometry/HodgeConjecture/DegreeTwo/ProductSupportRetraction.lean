import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPair

/-! # Product Support Retraction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProductSupportRetraction.Constructions

noncomputable section

section

/-!
# DegreeTwo: retract a product test while preserving tangential support

A relative test on a product, with complement pulled back from the
tangential factor, is exactly the pullback of its zero-normal restriction.
The actual normal contraction preserves that complement at every time.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy.Cohomology OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPair.Cycles

variable (E F : Type) [TopologicalSpace E] [TopologicalSpace F]

def tangentProjection : TopCat.of (E × F) ⟶ TopCat.of E :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

def tangentSection (z : F) : TopCat.of E ⟶ TopCat.of (E × F) :=
  TopCat.ofHom ⟨fun x => (x, z), continuous_id.prodMk continuous_const⟩

def tangentSupport (A : Set E) : Set (E × F) := Prod.fst ⁻¹' A

theorem tangentProjection_mapsTo (A : Set E) :
    Set.MapsTo (tangentProjection E F) (tangentSupport E F A) A := fun _ hx => hx

theorem tangentSection_mapsTo (z : F) (A : Set E) :
    Set.MapsTo (tangentSection E F z) A (tangentSupport E F A) := fun _ hx => hx

/-- Contract only the normal coordinate; the tangential support is fixed. -/
def tangentRetractionHomotopy (z : F)
    (H : ContinuousMap.Homotopy (ContinuousMap.const F z) (ContinuousMap.id F)) :
    TopCat.Homotopy (tangentProjection E F ≫ tangentSection E F z)
      (𝟙 (TopCat.of (E × F))) where
  toFun x := (x.2.1, H (x.1, x.2.2))
  continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
    (H.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  map_zero_left x := by simp [tangentProjection, tangentSection]
  map_one_left x := by simp

theorem tangentRetractionHomotopy_preserves (z : F)
    (H : ContinuousMap.Homotopy (ContinuousMap.const F z) (ContinuousMap.id F))
    (A : Set E) (t : unitInterval) :
    Set.MapsTo (fun x => tangentRetractionHomotopy E F z H (t, x))
      (tangentSupport E F A) (tangentSupport E F A) := fun _ hx => hx

variable {R : Type} [Ring R] (Q : ModuleCat.{0} R)

/-- The actual projection and zero section induce inverse relative
cohomology maps for every tangential support and every degree. -/
def tangentSupportCohomologyIso (z : F)
    (H : ContinuousMap.Homotopy (ContinuousMap.const F z) (ContinuousMap.id F)) (A : Set E) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology Q (TopCat.of E) A n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology Q (TopCat.of (E × F)) (tangentSupport E F A) n where
  hom := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (tangentProjection E F) (tangentProjection_mapsTo E F A) n
  inv := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (tangentSection E F z) (tangentSection_mapsTo E F z A) n
  hom_inv_id := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
    change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (𝟙 (TopCat.of E)) (fun _ hx => hx) n = _
    exact AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id Q (TopCat.of E) A n
  inv_hom_id := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
    have h := CycleClass.Geometric.RelativeCochainHomotopy.Cohomology.relativeSingularCohomologyMap_eq_of_homotopy Q
      (A := tangentSupport E F A) (B := tangentSupport E F A)
      (fun _ hx => hx) (fun _ hx => hx) (tangentRetractionHomotopy E F z H)
      (tangentRetractionHomotopy_preserves E F z H A) n
    exact h.trans (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id Q (TopCat.of (E × F)) (tangentSupport E F A) n)

/-- A genuine relative class on the product is recovered from its
actual restriction to the zero-normal slice. -/
theorem tangentSupport_class_eq_pullback (z : F)
    (H : ContinuousMap.Homotopy (ContinuousMap.const F z) (ContinuousMap.id F)) (A : Set E) (n : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology Q (TopCat.of (E × F)) (tangentSupport E F A) n) :
    b = AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (tangentProjection E F) (tangentProjection_mapsTo E F A) n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (tangentSection E F z) (tangentSection_mapsTo E F z A) n b) :=
  ((tangentSupportCohomologyIso E F Q z H A n).inv_hom_id_apply b).symm

def normalBallTangentSupportIso
    (T G : Type) [TopologicalSpace T] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Type} [Ring S] (Q : ModuleCat.{0} S) (r : ℝ) (hr : 0 < r) (A : Set T) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology Q (TopCat.of T) A n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology Q (TopCat.of (T × Metric.ball (0 : G) r))
        (tangentSupport T (Metric.ball (0 : G) r) A) n :=
  tangentSupportCohomologyIso T (Metric.ball (0 : G) r) Q
    ⟨0, Metric.mem_ball_self hr⟩
    (CycleClass.Geometric.NormalProductPair.Cycles.normalConvexContraction G (Metric.ball 0 r) (convex_ball 0 r) (Metric.mem_ball_self hr)) A n

end

/-! The actual product retraction for an arbitrary support in its second factor. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy.Cohomology OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPair.Cycles

set_option backward.isDefEq.respectTransparency false

variable (E F : Type) [TopologicalSpace E] [TopologicalSpace F]
variable {R : Type} [Ring R] (Q : ModuleCat.{0} R)

def secondSupportCohomologyIso (e : E)
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (A : Set F) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology Q (TopCat.of F) A n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology Q (TopCat.of (E×F)) (Prod.snd ⁻¹' A) n where
  hom := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (CycleClass.Geometric.NormalProductPair.Cycles.normalProductProjection E F)
    (A := Prod.snd ⁻¹' A) (B := A) (fun _ hx => hx) n
  inv := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection E F e)
    (A := A) (B := Prod.snd ⁻¹' A) (fun _ hx => hx) n
  hom_inv_id := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
    change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (𝟙 (TopCat.of F)) (fun _ hx => hx) n = _
    exact AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id Q (TopCat.of F) A n
  inv_hom_id := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
    have h := CycleClass.Geometric.RelativeCochainHomotopy.Cohomology.relativeSingularCohomologyMap_eq_of_homotopy Q
      (A := Prod.snd ⁻¹' A) (B := Prod.snd ⁻¹' A)
      (fun _ hx => hx) (fun _ hx => hx)
      (CycleClass.Geometric.NormalProductPair.Cycles.normalProductHomotopyOfContraction E F e H) (fun _ _ hx => hx) n
    exact h.trans (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id Q (TopCat.of (E×F)) (Prod.snd ⁻¹' A) n)

theorem secondSupport_class_eq_pullback (e : E)
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (A : Set F) (n : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology Q (TopCat.of (E×F)) (Prod.snd ⁻¹' A) n) :
    b = AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (CycleClass.Geometric.NormalProductPair.Cycles.normalProductProjection E F) (fun _ hx => hx) n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection E F e) (fun _ hx => hx) n b) :=
  ((secondSupportCohomologyIso E F Q e H A n).inv_hom_id_apply b).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProductSupportRetraction.Constructions
