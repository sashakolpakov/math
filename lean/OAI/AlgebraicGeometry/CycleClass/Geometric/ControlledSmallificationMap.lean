import OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledSmallification
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainSupport

/-! # Controlled Smallification Map -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles

noncomputable section

/-!
# A support-controlled inverse to the small-chain inclusion

The recursively constructed degree-raising correction defines an actual
null-homotopic chain map. Subtracting that map from the identity gives a
chain map whose image is small, and it therefore lifts uniquely through the
actual small-chain inclusion.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)
variable (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)

/-- The genuine correction family, zero outside the degree-raising diagonal. -/
def smallificationHomotopyComponent (i j : ℕ) :
    (LocalHomology.Cycles.integralSingularChains X).X i ⟶ (LocalHomology.Cycles.integralSingularChains X).X j :=
  if hij : i + 1 = j then
    ModuleCat.ofHom (ControlledSmallification.Cycles.smallificationHomotopyDegree X U hopen hcover i) ≫
      eqToHom (congrArg (LocalHomology.Cycles.integralSingularChains X).X hij)
  else 0

@[simp]
theorem smallificationHomotopyComponent_succ (n : ℕ) :
    smallificationHomotopyComponent X U hopen hcover n (n + 1) =
      ModuleCat.ofHom (ControlledSmallification.Cycles.smallificationHomotopyDegree X U hopen hcover n) := by
  simp [smallificationHomotopyComponent]

theorem smallificationHomotopyComponent_zero (i j : ℕ)
    (hij : ¬ (ComplexShape.down ℕ).Rel j i) :
    smallificationHomotopyComponent X U hopen hcover i j = 0 := by
  change ¬ i + 1 = j at hij
  simp [smallificationHomotopyComponent, hij]

/-- The identity minus the actual null-homotopic correction is a chain map. -/
def smallificationEndomorphism : LocalHomology.Cycles.integralSingularChains X ⟶ LocalHomology.Cycles.integralSingularChains X :=
  𝟙 _ - Homotopy.nullHomotopicMap (smallificationHomotopyComponent X U hopen hcover)

@[simp]
theorem smallificationEndomorphism_zero (c : (LocalHomology.Cycles.integralSingularChains X).X 0) :
    (smallificationEndomorphism X U hopen hcover).f 0 c = c := by
  change c - (dNext 0 (smallificationHomotopyComponent X U hopen hcover) +
    prevD 0 (smallificationHomotopyComponent X U hopen hcover)).hom c = c
  rw [Homotopy.dNext_zero_chainComplex, zero_add, Homotopy.prevD_chainComplex]
  simp only [smallificationHomotopyComponent_succ, ControlledSmallification.Cycles.smallificationHomotopyDegree_zero,
    ModuleCat.ofHom_zero, zero_comp, ModuleCat.hom_zero, LinearMap.zero_apply, sub_zero]

theorem smallificationEndomorphism_succ (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1)) :
    (smallificationEndomorphism X U hopen hcover).f (n + 1) c =
      c - ControlledSmallification.Cycles.smallificationHomotopyDegree X U hopen hcover n
        ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c) -
      (LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1)
        (ControlledSmallification.Cycles.smallificationHomotopyDegree X U hopen hcover (n + 1) c) := by
  change c - (dNext (n + 1) (smallificationHomotopyComponent X U hopen hcover) +
    prevD (n + 1) (smallificationHomotopyComponent X U hopen hcover)).hom c = _
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
  simp only [smallificationHomotopyComponent_succ, ModuleCat.hom_add,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.add_apply, LinearMap.comp_apply]
  abel

/-- Every component of the actual corrected chain map has small image. -/
theorem smallificationEndomorphism_small (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    (smallificationEndomorphism X U hopen hcover).f n c ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom := by
  cases n with
  | zero =>
    rw [smallificationEndomorphism_zero]
    exact ControlledSmallification.Cycles.zeroChain_mem_smallImage X U hopen hcover c
  | succ n =>
    rw [smallificationEndomorphism_succ]
    exact ControlledSmallification.Cycles.smallificationHomotopyDegree_residual_small X U hopen hcover n c

/-- The actual corrected chain map preserves every subspace-chain image. -/
theorem smallificationEndomorphism_subspace (n : ℕ) (A : Set X)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) (hc : c ∈ ControlledChainSupport.Cycles.singularSubspaceImage X A n) :
    (smallificationEndomorphism X U hopen hcover).f n c ∈ ControlledChainSupport.Cycles.singularSubspaceImage X A n := by
  cases n with
  | zero => simpa only [smallificationEndomorphism_zero] using hc
  | succ n =>
    rw [smallificationEndomorphism_succ]
    apply (ControlledChainSupport.Cycles.singularSubspaceImage X A (n + 1)).sub_mem
    · exact (ControlledChainSupport.Cycles.singularSubspaceImage X A (n + 1)).sub_mem hc
        (ControlledSmallification.Cycles.smallificationHomotopyDegree_subspace X U hopen hcover n A _
          (ControlledChainSupport.Cycles.singularSubspaceImage_boundary X A (n + 1) n hc))
    · exact ControlledChainSupport.Cycles.singularSubspaceImage_boundary X A (n + 2) (n + 1)
        (ControlledSmallification.Cycles.smallificationHomotopyDegree_subspace X U hopen hcover (n + 1) A c hc)

/-- Unique degreewise lifting of the actual corrected map to small chains. -/
def smallificationDegree (n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (SmallChainImage.Cycles.integralSmallSingularChains X U).X n :=
  LinearMap.codRestrictOfInjective
    ((smallificationEndomorphism X U hopen hcover).f n).hom
    ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom
    (SmallChainImage.Cycles.smallIntegralChainInclusion_injective X U n)
    (smallificationEndomorphism_small X U hopen hcover n)

@[simp]
theorem smallificationDegree_inclusion (n : ℕ) (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n (smallificationDegree X U hopen hcover n c) =
      (smallificationEndomorphism X U hopen hcover).f n c := by
  simp [smallificationDegree]

/-- The genuine support-controlled smallification chain map. -/
def smallificationChainMap : LocalHomology.Cycles.integralSingularChains X ⟶ SmallChainImage.Cycles.integralSmallSingularChains X U :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (smallificationDegree X U hopen hcover n))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply SmallChainImage.Cycles.smallIntegralChainInclusion_injective X U n
      change (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n
          ((SmallChainImage.Cycles.integralSmallSingularChains X U).d (n + 1) n
            (smallificationDegree X U hopen hcover (n + 1) c)) =
        (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n (smallificationDegree X U hopen hcover n
          ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c))
      rw [SmallSubdivision.Cycles.smallIntegralChainInclusion_d, smallificationDegree_inclusion,
        smallificationDegree_inclusion]
      exact ConcreteCategory.congr_hom
        ((smallificationEndomorphism X U hopen hcover).comm (n + 1) n) c)

@[simp]
theorem smallificationChainMap_f (n : ℕ) :
    ((smallificationChainMap X U hopen hcover).f n).hom =
      smallificationDegree X U hopen hcover n := rfl

@[reassoc (attr := simp)]
theorem smallificationChainMap_inclusion :
    smallificationChainMap X U hopen hcover ≫ SmallChainImage.Cycles.smallIntegralChainInclusion X U =
      smallificationEndomorphism X U hopen hcover := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact smallificationDegree_inclusion X U hopen hcover n c

/-- The identity is homotopic to inclusion after actual smallification, with
the previously constructed support-controlled components. -/
def smallificationAmbientHomotopy :
    Homotopy (𝟙 (LocalHomology.Cycles.integralSingularChains X))
      (smallificationChainMap X U hopen hcover ≫ SmallChainImage.Cycles.smallIntegralChainInclusion X U) where
  hom := smallificationHomotopyComponent X U hopen hcover
  zero := smallificationHomotopyComponent_zero X U hopen hcover
  comm n := by
    rw [smallificationChainMap_inclusion]
    change (𝟙 ((LocalHomology.Cycles.integralSingularChains X).X n)) =
      dNext n (smallificationHomotopyComponent X U hopen hcover) +
      prevD n (smallificationHomotopyComponent X U hopen hcover) +
      ((𝟙 ((LocalHomology.Cycles.integralSingularChains X).X n)) -
        (dNext n (smallificationHomotopyComponent X U hopen hcover) +
          prevD n (smallificationHomotopyComponent X U hopen hcover)))
    abel

/-- Each nonzero simplex created by the homotopy lies inside the image of
the input simplex, as an explicit geometric support statement. -/
theorem smallificationHomotopyDegree_simplex_support (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌))
    (τ : (TopCat.toSSet.obj X).obj (.op ⦋n + 1⦌))
    (hτ : SingularChainSupport.Cycles.singularChainCoefficients X (n + 1)
      (ControlledSmallification.Cycles.smallificationHomotopyDegree X U hopen hcover n
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ 1)) τ ≠ 0) :
    Set.range (X.toSSetObjEquiv (.op ⦋n + 1⦌) τ) ⊆
      Set.range (X.toSSetObjEquiv (.op ⦋n⦌) σ) :=
  (RelativeChainSupport.Cycles.mem_subspaceChainInclusion_range_iff X _ (n + 1) _).mp
    (ControlledSmallification.Cycles.smallificationHomotopyDegree_subspace X U hopen hcover n _ _
      (ControlledChainSupport.Cycles.singularSimplex_mem_subspaceImage X _ n σ Set.Subset.rfl 1)) τ hτ

/-- Smallification itself has the same explicit geometric support control. -/
theorem smallificationChainMap_simplex_support (n : ℕ)
    (σ τ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌))
    (hτ : SingularChainSupport.Cycles.singularChainCoefficients X n
      ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n
        ((smallificationChainMap X U hopen hcover).f n
          ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ 1))) τ ≠ 0) :
    Set.range (X.toSSetObjEquiv (.op ⦋n⦌) τ) ⊆
      Set.range (X.toSSetObjEquiv (.op ⦋n⦌) σ) := by
  change SingularChainSupport.Cycles.singularChainCoefficients X n
    ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n (smallificationDegree X U hopen hcover n _)) τ ≠ 0 at hτ
  rw [smallificationDegree_inclusion] at hτ
  exact (RelativeChainSupport.Cycles.mem_subspaceChainInclusion_range_iff X _ n _).mp
    (smallificationEndomorphism_subspace X U hopen hcover n _ _
      (ControlledChainSupport.Cycles.singularSimplex_mem_subspaceImage X _ n σ Set.Subset.rfl 1)) τ hτ

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap.Cycles
