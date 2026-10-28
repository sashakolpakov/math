import OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledChainSupport
import OAI.AlgebraicGeometry.CycleClass.Geometric.IteratedSubdivisionHomotopy

/-! # Controlled Smallification -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledSmallification.Cycles

noncomputable section

section

/-!
# Small-chain replacement with spatial support control

The replacement is constructed from the actual iterated barycentric
subdivision and its proved prism homotopy. The exponent may depend on the
finite chain; no uniform exponent for locally finite chains is asserted.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)
variable (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)

include hopen hcover

/-- Every zero-chain is already small for an open cover. -/
theorem zeroChain_mem_smallImage (c : (LocalHomology.Cycles.integralSingularChains X).X 0) :
    c ∈ LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f 0).hom := by
  obtain ⟨N, b, hb⟩ :=
    SmallChainImage.Cycles.exists_subdivisionDegree_iterate_smallChain_preimage X U hopen hcover c
  have hN : ∀ M : ℕ, (SubdivisionOperator.Cycles.subdivisionDegree X 0)^[M] c = c := by
    intro M
    induction M with
    | zero => rfl
    | succ M ih =>
      simpa only [Function.iterate_succ_apply', SubdivisionNaturality.Cycles.subdivisionDegree_zero_dimension_apply] using ih
  exact ⟨b, hb.trans (hN N)⟩

/-- A positive-degree chain with small boundary admits a small replacement
with the same boundary. The bounding correction and replacement remain in
every subspace in which the original chain is supported. -/
theorem exists_controlledSmallReplacement (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1))
    (hc : (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom) :
    ∃ (b : (SmallChainImage.Cycles.integralSmallSingularChains X U).X (n + 1))
      (D : (LocalHomology.Cycles.integralSingularChains X).X (n + 2)),
      c - (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f (n + 1) b =
        (LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1) D ∧
      ∀ A : Set X, c ∈ ControlledChainSupport.Cycles.singularSubspaceImage X A (n + 1) →
        D ∈ ControlledChainSupport.Cycles.singularSubspaceImage X A (n + 2) ∧
        (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f (n + 1) b ∈
          ControlledChainSupport.Cycles.singularSubspaceImage X A (n + 1) := by
  obtain ⟨N, b, hb⟩ :=
    SmallSubdivision.Cycles.exists_subdivisionChainMap_iterate_small_preimage X U hopen hcover c
  have hb' : (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f (n + 1) b =
      (EventuallySmall.Cycles.iterateChainMap (SubdivisionBoundary.Cycles.subdivisionChainMap X) N).f (n + 1) c := by
    rw [EventuallySmall.Cycles.iterateChainMap_apply]
    exact hb
  obtain ⟨a, ha⟩ := IteratedSubdivisionHomotopy.Cycles.subdivisionPrism_preserves_smallChainImage X U N n hc
  have hsum : (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f (n + 1) (b + a) =
      (EventuallySmall.Cycles.iterateChainMap (SubdivisionBoundary.Cycles.subdivisionChainMap X) N).f (n + 1) c +
        IteratedSubdivisionHomotopy.Cycles.subdivisionPrism X N n ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c) := by
    rw [map_add, hb', ha]
  have hbound : c - (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f (n + 1) (b + a) =
      (LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1)
        (IteratedSubdivisionHomotopy.Cycles.subdivisionPrism X N (n + 1) c) := by
    rw [hsum]
    exact IteratedSubdivisionHomotopy.Cycles.subdivisionPrism_boundary_correction X N n c
  refine ⟨b + a, IteratedSubdivisionHomotopy.Cycles.subdivisionPrism X N (n + 1) c, hbound, ?_⟩
  intro A hA
  have hD := IteratedSubdivisionHomotopy.Cycles.subdivisionPrism_preserves_subspaceImage X A N (n + 1) hA
  refine ⟨hD, ?_⟩
  have hreplace : (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f (n + 1) (b + a) =
      c - (LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1)
        (IteratedSubdivisionHomotopy.Cycles.subdivisionPrism X N (n + 1) c) := by
    rw [← hbound]
    abel
  rw [hreplace]
  exact (ControlledChainSupport.Cycles.singularSubspaceImage X A (n + 1)).sub_mem hA
    (ControlledChainSupport.Cycles.singularSubspaceImage_boundary X A (n + 2) (n + 1) hD)

/-- A useful equivalent form chooses only the support-controlled bounding
correction; the corrected chain lies in the actual small-chain image. -/
theorem exists_controlledSmallCorrection (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1))
    (hc : (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom) :
    ∃ D : (LocalHomology.Cycles.integralSingularChains X).X (n + 2),
      c - (LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1) D ∈
        LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f (n + 1)).hom ∧
      ∀ A : Set X, c ∈ ControlledChainSupport.Cycles.singularSubspaceImage X A (n + 1) →
        D ∈ ControlledChainSupport.Cycles.singularSubspaceImage X A (n + 2) := by
  obtain ⟨b, D, hb, hD⟩ := exists_controlledSmallReplacement X U hopen hcover n c hc
  refine ⟨D, ⟨b, ?_⟩, fun A hA => (hD A hA).1⟩
  rw [← hb]
  abel

/-- A chosen bounding correction with the proved simultaneous support control. -/
def controlledSmallCorrection (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1))
    (hc : (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom) :
    (LocalHomology.Cycles.integralSingularChains X).X (n + 2) :=
  Classical.choose (exists_controlledSmallCorrection X U hopen hcover n c hc)

theorem controlledSmallCorrection_small (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1))
    (hc : (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom) :
    c - (LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1)
      (controlledSmallCorrection X U hopen hcover n c hc) ∈
        LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f (n + 1)).hom :=
  (Classical.choose_spec (exists_controlledSmallCorrection X U hopen hcover n c hc)).1

theorem controlledSmallCorrection_subspace (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1))
    (hc : (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom)
    (A : Set X) (hA : c ∈ ControlledChainSupport.Cycles.singularSubspaceImage X A (n + 1)) :
    controlledSmallCorrection X U hopen hcover n c hc ∈
      ControlledChainSupport.Cycles.singularSubspaceImage X A (n + 2) :=
  (Classical.choose_spec (exists_controlledSmallCorrection X U hopen hcover n c hc)).2 A hA

end

/-!
# Recursive support-controlled corrections on singular chains

In each degree a separate finite subdivision is chosen for each singular
simplex. The resulting generator values extend linearly. The induction keeps
the boundary correction small and preserves every actual subspace image.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The proved induction invariant for a degree-raising correction. -/
structure ControlledSmallificationStage (X : TopCat.{0}) {J : Type}
    (U : J → Set X) (n : ℕ) where
  hom : (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (LocalHomology.Cycles.integralSingularChains X).X (n + 1)
  preserves_subspace : ∀ (A : Set X) (c : (LocalHomology.Cycles.integralSingularChains X).X n),
    c ∈ ControlledChainSupport.Cycles.singularSubspaceImage X A n → hom c ∈ ControlledChainSupport.Cycles.singularSubspaceImage X A (n + 1)
  boundary_small : ∀ c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1),
    (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c -
      (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
        (hom ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c)) ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)
variable (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)

/-- The zero-degree correction is zero because all zero-chains are small. -/
def controlledSmallificationBase : ControlledSmallificationStage X U 0 where
  hom := 0
  preserves_subspace A _ _ := (ControlledChainSupport.Cycles.singularSubspaceImage X A 1).zero_mem
  boundary_small c := by
    simpa only [LinearMap.zero_apply, map_zero, sub_zero] using
      zeroChain_mem_smallImage X U hopen hcover ((LocalHomology.Cycles.integralSingularChains X).d 1 0 c)

/-- Remove the previously constructed correction to the boundary of a simplex. -/
def correctedSingularSimplex {n : ℕ} (p : ControlledSmallificationStage X U n)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n + 1⦌)) :
    (LocalHomology.Cycles.integralSingularChains X).X (n + 1) :=
  let g : (LocalHomology.Cycles.integralSingularChains X).X (n + 1) :=
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ 1
  g - p.hom ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n g)

theorem correctedSingularSimplex_boundary_small {n : ℕ}
    (p : ControlledSmallificationStage X U n)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n + 1⦌)) :
    (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n (correctedSingularSimplex X U p σ) ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom := by
  unfold correctedSingularSimplex
  rw [map_sub]
  exact p.boundary_small _

theorem correctedSingularSimplex_subspace {n : ℕ}
    (p : ControlledSmallificationStage X U n)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n + 1⦌)) :
    correctedSingularSimplex X U p σ ∈ ControlledChainSupport.Cycles.singularSubspaceImage X
      (Set.range (X.toSSetObjEquiv (.op ⦋n + 1⦌) σ)) (n + 1) := by
  let A := Set.range (X.toSSetObjEquiv (.op ⦋n + 1⦌) σ)
  have hσ := ControlledChainSupport.Cycles.singularSimplex_mem_subspaceImage X A (n + 1) σ Set.Subset.rfl (1 : ℤ)
  exact (ControlledChainSupport.Cycles.singularSubspaceImage X A (n + 1)).sub_mem hσ
    (p.preserves_subspace A _ (ControlledChainSupport.Cycles.singularSubspaceImage_boundary X A (n + 1) n hσ))

/-- Choose the proved finite correction independently on each simplex. -/
def nextSmallificationGenerator {n : ℕ} (p : ControlledSmallificationStage X U n)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n + 1⦌)) :
    (LocalHomology.Cycles.integralSingularChains X).X (n + 2) :=
  controlledSmallCorrection X U hopen hcover n (correctedSingularSimplex X U p σ)
    (correctedSingularSimplex_boundary_small X U p σ)

theorem nextSmallificationGenerator_subspace {n : ℕ}
    (p : ControlledSmallificationStage X U n)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n + 1⦌)) :
    nextSmallificationGenerator X U hopen hcover p σ ∈ ControlledChainSupport.Cycles.singularSubspaceImage X
      (Set.range (X.toSSetObjEquiv (.op ⦋n + 1⦌) σ)) (n + 2) :=
  controlledSmallCorrection_subspace X U hopen hcover n _ _ _
    (correctedSingularSimplex_subspace X U p σ)

/-- Linear extension of the independently chosen, support-controlled simplex corrections. -/
def nextSmallificationHom {n : ℕ} (p : ControlledSmallificationStage X U n) :
    (LocalHomology.Cycles.integralSingularChains X).X (n + 1) →ₗ[ℤ] (LocalHomology.Cycles.integralSingularChains X).X (n + 2) :=
  ControlledChainSupport.Cycles.singularLinearExtension X (n + 1) ((LocalHomology.Cycles.integralSingularChains X).X (n + 2))
    (nextSmallificationGenerator X U hopen hcover p)

/-- The new correction makes the entire residual small, by linear extension
of the proved correction identity on actual simplex generators. -/
theorem nextSmallificationHom_small {n : ℕ} (p : ControlledSmallificationStage X U n)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1)) :
    c - p.hom ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c) -
      (LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1)
        (nextSmallificationHom X U hopen hcover p c) ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f (n + 1)).hom := by
  let F : (LocalHomology.Cycles.integralSingularChains X).X (n + 1) →ₗ[ℤ]
      (LocalHomology.Cycles.integralSingularChains X).X (n + 1) :=
    LinearMap.id - p.hom.comp ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n).hom -
      ((LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1)).hom.comp
        (nextSmallificationHom X U hopen hcover p)
  apply ControlledChainSupport.Cycles.singularLinearMap_mem_one X (n + 1) ((LocalHomology.Cycles.integralSingularChains X).X (n + 1))
    (LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f (n + 1)).hom) F _ c
  intro σ
  dsimp only [F, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
  rw [nextSmallificationHom, ControlledChainSupport.Cycles.singularLinearExtension_simplex, one_zsmul]
  exact controlledSmallCorrection_small X U hopen hcover n
    (correctedSingularSimplex X U p σ) (correctedSingularSimplex_boundary_small X U p σ)

/-- The induction step proves, rather than assumes, the next invariant. -/
def controlledSmallificationStep {n : ℕ} (p : ControlledSmallificationStage X U n) :
    ControlledSmallificationStage X U (n + 1) where
  hom := nextSmallificationHom X U hopen hcover p
  preserves_subspace A c hc :=
    ControlledChainSupport.Cycles.singularLinearExtension_subspace X (n + 1) (n + 2)
      (nextSmallificationGenerator X U hopen hcover p)
      (nextSmallificationGenerator_subspace X U hopen hcover p) A hc
  boundary_small c := by
    have h := nextSmallificationHom_small X U hopen hcover p
      ((LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1) c)
    have hdd : (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
        ((LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1) c) = 0 :=
      ConcreteCategory.congr_hom ((LocalHomology.Cycles.integralSingularChains X).d_comp_d (n + 2) (n + 1) n) c
    simpa only [hdd, map_zero, sub_zero] using h

/-- The actual sequence of proved correction stages in all chain degrees. -/
def controlledSmallificationStages (n : ℕ) : ControlledSmallificationStage X U n :=
  Nat.rec (motive := fun k => ControlledSmallificationStage X U k)
    (controlledSmallificationBase X U hopen hcover)
    (fun _ p => controlledSmallificationStep X U hopen hcover p) n

/-- The degree-raising correction constructed on actual singular chains. -/
def smallificationHomotopyDegree (n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (LocalHomology.Cycles.integralSingularChains X).X (n + 1) :=
  (controlledSmallificationStages X U hopen hcover n).hom

theorem smallificationHomotopyDegree_subspace (n : ℕ) (A : Set X)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) (hc : c ∈ ControlledChainSupport.Cycles.singularSubspaceImage X A n) :
    smallificationHomotopyDegree X U hopen hcover n c ∈ ControlledChainSupport.Cycles.singularSubspaceImage X A (n + 1) :=
  (controlledSmallificationStages X U hopen hcover n).preserves_subspace A c hc

@[simp]
theorem smallificationHomotopyDegree_zero :
    smallificationHomotopyDegree X U hopen hcover 0 = 0 := rfl

/-- In every positive degree the constructed homotopy leaves a small residual. -/
theorem smallificationHomotopyDegree_residual_small (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1)) :
    c - smallificationHomotopyDegree X U hopen hcover n
        ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c) -
      (LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1)
        (smallificationHomotopyDegree X U hopen hcover (n + 1) c) ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f (n + 1)).hom :=
  nextSmallificationHom_small X U hopen hcover
    (controlledSmallificationStages X U hopen hcover n) c

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledSmallification.Cycles
