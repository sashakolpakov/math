import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPair
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-! # Normal Product Cohomology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductCohomology

noncomputable section

/-!
# Actual relative cohomology of the normal product pair

The cochain maps are the actual pullbacks of the normal projection and a
constant tangential section. Their homotopy identities use the displayed
homotopy of pairs, with no assumed Thom or cohomology comparison class.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Matrix

set_option backward.isDefEq.respectTransparency false

namespace Cycles

open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy.Cohomology

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)

section PointedProduct

variable (E F : Type) [TopologicalSpace E] [TopologicalSpace F]

/-- A contraction of the tangential factor gives the actual contravariant
homotopy equivalence of relative singular cochain complexes. -/
def normalProductCochainEquivOfContraction (e : E) (z : F)
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E)) :
    HomotopyEquiv
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M (TopCat.of F) ({z}ᶜ : Set F))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M (TopCat.of (E × F)) (NormalProductPair.Cycles.normalProductComplement E F z)) where
  hom := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (NormalProductPair.Cycles.normalProductProjection E F)
    (NormalProductPair.Cycles.normalProductProjection_mapsTo E F z)
  inv := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (NormalProductPair.Cycles.normalProductSection E F e)
    (NormalProductPair.Cycles.normalProductSection_mapsTo E F e z)
  homotopyHomInvId := by
    apply Homotopy.ofEq
    rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp]
    change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (𝟙 (TopCat.of F))
      (A := ({z}ᶜ : Set F)) (B := ({z}ᶜ : Set F)) (fun _ hx => hx) = _
    exact AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_id M _ _
  homotopyInvHomId := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp]
    have h := RelativeCochainHomotopy.Cohomology.relativeSingularCochainsHomotopy M
      (A := NormalProductPair.Cycles.normalProductComplement E F z) (B := NormalProductPair.Cycles.normalProductComplement E F z)
      (fun _ hx => hx) (fun _ hx => hx)
      (NormalProductPair.Cycles.normalProductHomotopyOfContraction E F e H)
      (NormalProductPair.Cycles.normalProductHomotopyOfContraction_mapsTo E F e z H)
    simpa only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_id] using h

/-- The genuine relative cohomology equivalence for a contracted tangential factor. -/
def normalProductCohomologyIsoOfContraction (e : E) (z : F)
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E)) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of F) ({z}ᶜ : Set F) n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of (E × F)) (NormalProductPair.Cycles.normalProductComplement E F z) n :=
  (normalProductCochainEquivOfContraction M E F e z H).toHomologyIso n

@[simp]
theorem normalProductCohomologyIsoOfContraction_hom (e : E) (z : F)
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E)) (n : ℕ) :
    (normalProductCohomologyIsoOfContraction M E F e z H n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (NormalProductPair.Cycles.normalProductProjection E F)
        (NormalProductPair.Cycles.normalProductProjection_mapsTo E F z) n := rfl

@[simp]
theorem normalProductCohomologyIsoOfContraction_inv (e : E) (z : F)
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E)) (n : ℕ) :
    (normalProductCohomologyIsoOfContraction M E F e z H n).inv =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (NormalProductPair.Cycles.normalProductSection E F e)
        (NormalProductPair.Cycles.normalProductSection_mapsTo E F e z) n := rfl

/-- Pullback from the normal model restricts to the same class on every
constant tangential fiber, already at the cochain level. -/
theorem normalProductCochains_fiber (e : E) (z : F) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (NormalProductPair.Cycles.normalProductProjection E F)
        (NormalProductPair.Cycles.normalProductProjection_mapsTo E F z) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (NormalProductPair.Cycles.normalProductSection E F e)
        (NormalProductPair.Cycles.normalProductSection_mapsTo E F e z) = 𝟙 _ := by
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp]
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (𝟙 (TopCat.of F))
    (A := ({z}ᶜ : Set F)) (B := ({z}ᶜ : Set F)) (fun _ hx => hx) = _
  exact AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_id M _ _

/-- Fiberwise normalization is unchanged on genuine relative cohomology. -/
theorem normalProductCohomology_fiber (e : E) (z : F) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (NormalProductPair.Cycles.normalProductProjection E F)
        (NormalProductPair.Cycles.normalProductProjection_mapsTo E F z) n ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (NormalProductPair.Cycles.normalProductSection E F e)
        (NormalProductPair.Cycles.normalProductSection_mapsTo E F e z) n = 𝟙 _ := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
  rw [← HomologicalComplex.homologyMap_comp, normalProductCochains_fiber,
    HomologicalComplex.homologyMap_id]

end PointedProduct

section LinearTangent

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (F : Type) [TopologicalSpace F]

/-- The actual relative cochain homotopy equivalence of the linear normal product. -/
def normalProductCochainEquiv (z : F) :
    HomotopyEquiv
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M (TopCat.of F) ({z}ᶜ : Set F))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M (TopCat.of (E × F)) (NormalProductPair.Cycles.normalProductComplement E F z)) :=
  normalProductCochainEquivOfContraction M E F 0 z (NormalProductPair.Cycles.normalLinearContraction E)

/-- The normal product-pair cohomology is the actual punctured-normal cohomology. -/
def normalProductCohomologyIso (z : F) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of F) ({z}ᶜ : Set F) n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of (E × F)) (NormalProductPair.Cycles.normalProductComplement E F z) n :=
  (normalProductCochainEquiv M E F z).toHomologyIso n

@[simp]
theorem normalProductCohomologyIso_hom (z : F) (n : ℕ) :
    (normalProductCohomologyIso M E F z n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (NormalProductPair.Cycles.normalProductProjection E F)
        (NormalProductPair.Cycles.normalProductProjection_mapsTo E F z) n := rfl

@[simp]
theorem normalProductCohomologyIso_inv (z : F) (n : ℕ) :
    (normalProductCohomologyIso M E F z n).inv =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (NormalProductPair.Cycles.normalProductSection E F 0)
        (NormalProductPair.Cycles.normalProductSection_mapsTo E F 0 z) n := rfl

/-- Every constant tangential section gives the same inverse cohomology map. -/
theorem normalProductCohomologyIso_inv_eq_section (e : E) (z : F) (n : ℕ) :
    (normalProductCohomologyIso M E F z n).inv =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (NormalProductPair.Cycles.normalProductSection E F e)
        (NormalProductPair.Cycles.normalProductSection_mapsTo E F e z) n := by
  apply (cancel_epi (normalProductCohomologyIso M E F z n).hom).mp
  rw [Iso.hom_inv_id, normalProductCohomologyIso_hom, normalProductCohomology_fiber]

/-- A convex tangential neighborhood gives the same actual cohomology model. -/
def normalConvexProductCohomologyIso (U : Set E) (hU : Convex ℝ U) (h0 : (0 : E) ∈ U)
    (z : F) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of F) ({z}ᶜ : Set F) n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of (U × F)) (NormalProductPair.Cycles.normalProductComplement U F z) n :=
  normalProductCohomologyIsoOfContraction M U F ⟨0, h0⟩ z (NormalProductPair.Cycles.normalConvexContraction E U hU h0) n

/-- The actual cohomology equivalence over an open tangential ball. -/
def normalOpenBallProductCohomologyIso (r : ℝ) (hr : 0 < r) (z : F) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of F) ({z}ᶜ : Set F) n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of (Metric.ball (0 : E) r × F))
        (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) F z) n :=
  normalConvexProductCohomologyIso M E F (Metric.ball 0 r) (convex_ball 0 r)
    (Metric.mem_ball_self hr) z n

end LinearTangent

section TwoBalls

/-- An actual homeomorphism of pointed spaces gives an actual isomorphism
of the relative cochain kernels. -/
def normalPointedHomeomorphCochainIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M (TopCat.of Y) ({e x}ᶜ : Set Y) ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M (TopCat.of X) ({x}ᶜ : Set X) := by
  let f : TopCat.of X ⟶ TopCat.of Y := (TopCat.isoOfHomeo e).hom
  let g : TopCat.of Y ⟶ TopCat.of X := (TopCat.isoOfHomeo e).inv
  have hf : Set.MapsTo f ({x}ᶜ : Set X) ({e x}ᶜ : Set Y) := by
    intro y hy
    change e y ≠ e x
    exact fun h => hy (e.injective h)
  have hg : Set.MapsTo g ({e x}ᶜ : Set Y) ({x}ᶜ : Set X) := by
    intro y hy
    change e.symm y ≠ x
    intro h
    apply hy
    simpa using congrArg e h
  exact {
    hom := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f hf
    inv := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M g hg
    hom_inv_id := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id M g f hg hf
      (by ext y; exact e.apply_symm_apply y)
    inv_hom_id := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id M f g hf hg
      (by ext y; exact e.symm_apply_apply y) }

variable (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The explicit radial unit-ball homeomorphism followed by positive scaling. -/
def normalOpenBallHomeomorph (s : ℝ) (hs : 0 < s) : F ≃ₜ Metric.ball (0 : F) s :=
  Homeomorph.unitBall.trans
    ((Homeomorph.smulOfNeZero s hs.ne').subtype (by
      intro x
      change dist x 0 < 1 ↔ dist (s • x) 0 < s
      rw [dist_zero_right, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
      constructor <;> intro h <;> nlinarith))

@[simp]
theorem normalOpenBallHomeomorph_zero (s : ℝ) (hs : 0 < s) :
    normalOpenBallHomeomorph F s hs 0 = ⟨0, Metric.mem_ball_self hs⟩ := by
  apply Subtype.ext
  change s • (Homeomorph.unitBall (0 : F) : F) = 0
  rw [Homeomorph.coe_unitBall_apply_zero, smul_zero]

/-- Actual pointed-ball cohomology identifies with the full normal model
through the displayed radial homeomorphism. -/
def normalOpenBallCohomologyIso (s : ℝ) (hs : 0 < s) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of F) ({0}ᶜ : Set F) n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of (Metric.ball (0 : F) s))
        ({⟨0, Metric.mem_ball_self hs⟩}ᶜ : Set (Metric.ball (0 : F) s)) n := by
  have e := (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapIso
    (normalPointedHomeomorphCochainIso M (normalOpenBallHomeomorph F s hs) 0).symm
  simpa only [AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology, HomologicalComplex.homologyFunctor_obj,
    normalOpenBallHomeomorph_zero] using e

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual relative cohomology equivalence for two open product balls.
Its normal factor uses the explicit pointed radial homeomorphism above. -/
def normalOpenProductBallsCohomologyIso (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of F) ({0}ᶜ : Set F) n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M
        (TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : F) s))
        (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
          ⟨0, Metric.mem_ball_self hs⟩) n :=
  normalOpenBallCohomologyIso M F s hs n ≪≫
    normalOpenBallProductCohomologyIso M E (Metric.ball (0 : F) s) r hr
      ⟨0, Metric.mem_ball_self hs⟩ n

end TwoBalls

variable (E : Type) [TopologicalSpace E]
variable {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (hA : IsUnit A)

/-- Invertible complex changes of the normal coordinates act identically on
the genuine relative cohomology, with arbitrary module coefficients. -/
theorem normalProductComplexChange_cohomology_eq_id (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (NormalProductPair.Cycles.normalProductComplexChange E A)
      (NormalProductPair.Cycles.normalProductComplexChange_mapsTo E A hA) n = 𝟙 _ := by
  have h := RelativeCochainHomotopy.Cohomology.relativeSingularCohomologyMap_eq_of_homotopy M
    (A := NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0)
    (B := NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0)
    (fun _ hx => hx) (NormalProductPair.Cycles.normalProductComplexChange_mapsTo E A hA)
    (NormalProductPair.Cycles.normalProductComplexChangeHomotopy E A hA)
    (NormalProductPair.Cycles.normalProductComplexChangeHomotopy_mapsTo E A hA) n
  simpa only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id] using h.symm

/-- Thus every relative class transported from the normal model is invariant
under invertible complex normal-coordinate changes. -/
theorem normalProductComplexChange_class_invariant (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of (E × (Fin p → ℂ)))
      (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0) n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (NormalProductPair.Cycles.normalProductComplexChange E A)
      (NormalProductPair.Cycles.normalProductComplexChange_mapsTo E A hA) n).hom c = c := by
  rw [normalProductComplexChange_cohomology_eq_id M E A hA]
  rfl

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductCohomology
