import OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives
import OAI.AlgebraicTopology.Cohomology.Singular.ChainDual

/-! # Evaluation -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Evaluation

noncomputable section

/-!
# Evaluation of singular cohomology on singular homology

The pairing descends the actual linear evaluation of a singular cochain on a
singular chain. The chain/cochain differential identity proves both required
independence statements: cocycles vanish on boundaries and coboundaries vanish
on cycles. No arbitrary pairing is supplied as an assumption.
-/

open _root_.CategoryTheory

variable {R : Type} [CommRing R]

/-- Scalar singular chains on the genuine continuous singular simplicial set. -/
abbrev singularScalarChains (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} R) ℕ :=
  ChainDual.simplicialScalarChains (R := R) (TopCat.toSSet.obj X)

/-- Every outgoing differential vanishes on a cocycle, including off-shape ones. -/
theorem cochainCocycle_d_eq_zero (C : CochainComplex (ModuleCat.{0} R) ℕ)
    (n i : ℕ) (c : Representatives.cochainCocycles C n) : (C.d n i) (c : C.X n) = 0 := by
  by_cases h : (ComplexShape.up ℕ).Rel n i
  · have hc : (C.d n ((ComplexShape.up ℕ).next n)) (c : C.X n) = 0 := c.property
    have hi : (ComplexShape.up ℕ).next n = i := (ComplexShape.up ℕ).next_eq' h
    rw [hi] at hc
    exact hc
  · rw [C.shape n i h]
    rfl

/-- A genuine cocycle evaluates to zero on every genuine boundary. -/
theorem cocycle_evaluation_boundary (K : SSet.{0}) (M : ModuleCat.{0} R)
    (n i : ℕ) (c : Representatives.cochainCocycles (Basic.simplicialCochains K M) n)
    (z : (ChainDual.simplicialScalarChains (R := R) K).X i) :
    ChainDual.degreewiseChainDualEquiv K M n (c : (Basic.simplicialCochains K M).X n)
      ((ChainDual.simplicialScalarChains (R := R) K).d i n z) = 0 := by
  have h := LinearMap.congr_fun
    (ChainDual.degreewiseChainDualEquiv_d K M n i (c : (Basic.simplicialCochains K M).X n)) z
  have hc := cochainCocycle_d_eq_zero (Basic.simplicialCochains K M) n i c
  simpa only [hc, map_zero, LinearMap.zero_apply, LinearMap.comp_apply] using h.symm

/-- A genuine coboundary evaluates to zero on every genuine cycle. -/
theorem coboundary_evaluation_cycle (K : SSet.{0}) (M : ModuleCat.{0} R)
    (i n : ℕ) (c : (Basic.simplicialCochains K M).X i)
    (z : ChainRepresentatives.chainCycles (ChainDual.simplicialScalarChains (R := R) K) n) :
    ChainDual.degreewiseChainDualEquiv K M n ((Basic.simplicialCochains K M).d i n c)
      (z : (ChainDual.simplicialScalarChains (R := R) K).X n) = 0 := by
  have h := LinearMap.congr_fun (ChainDual.degreewiseChainDualEquiv_d K M i n c)
    (z : (ChainDual.simplicialScalarChains (R := R) K).X n)
  simpa only [LinearMap.comp_apply,
    ChainRepresentatives.chainCycle_d_eq_zero (ChainDual.simplicialScalarChains (R := R) K) n i z, map_zero] using h

/-- A cocycle's evaluation, descended to actual categorical homology. -/
def evaluateCocycle (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ)
    (c : Representatives.cochainCocycles (Basic.simplicialCochains K M) n) :
    (ChainDual.simplicialScalarChains (R := R) K).homology n →ₗ[R] M :=
  ((ChainRepresentatives.chainBoundaries (ChainDual.simplicialScalarChains (R := R) K) n).liftQ
    ((ChainDual.degreewiseChainDualEquiv K M n (c : (Basic.simplicialCochains K M).X n)).comp
      (ChainRepresentatives.chainCycles (ChainDual.simplicialScalarChains (R := R) K) n).subtype)
    (by
      intro z hz
      rcases hz with ⟨w, rfl⟩
      change ChainDual.degreewiseChainDualEquiv K M n (c : (Basic.simplicialCochains K M).X n)
        (((ChainDual.simplicialScalarChains (R := R) K).sc n).f w) = 0
      exact cocycle_evaluation_boundary K M n _ c w)).comp
    (ChainRepresentatives.homologyQuotientIso (ChainDual.simplicialScalarChains (R := R) K) n).toLinearEquiv.toLinearMap

@[simp]
theorem evaluateCocycle_chainClass (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ)
    (c : Representatives.cochainCocycles (Basic.simplicialCochains K M) n)
    (z : ChainRepresentatives.chainCycles (ChainDual.simplicialScalarChains (R := R) K) n) :
    evaluateCocycle K M n c (ChainRepresentatives.chainClass (ChainDual.simplicialScalarChains (R := R) K) n z) =
      ChainDual.degreewiseChainDualEquiv K M n (c : (Basic.simplicialCochains K M).X n)
        (z : (ChainDual.simplicialScalarChains (R := R) K).X n) := by
  dsimp only [evaluateCocycle, ChainRepresentatives.chainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- Evaluation on homology is linear in the cocycle. -/
def cocycleHomologyEvaluation (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ) :
    Representatives.cochainCocycles (Basic.simplicialCochains K M) n →ₗ[R]
      ((ChainDual.simplicialScalarChains (R := R) K).homology n →ₗ[R] M) where
  toFun := evaluateCocycle K M n
  map_add' c d := by
    ext h
    obtain ⟨z, rfl⟩ := ChainRepresentatives.chainClass_surjective (ChainDual.simplicialScalarChains (R := R) K) n h
    simp only [evaluateCocycle_chainClass, LinearMap.add_apply, Submodule.coe_add, map_add]
  map_smul' r c := by
    ext h
    obtain ⟨z, rfl⟩ := ChainRepresentatives.chainClass_surjective (ChainDual.simplicialScalarChains (R := R) K) n h
    simp only [evaluateCocycle_chainClass, LinearMap.smul_apply, Submodule.coe_smul,
      map_smul, RingHom.id_apply]

/-- Changing the cocycle by a coboundary does not change evaluation on homology. -/
@[simp]
theorem cocycleHomologyEvaluation_boundary (K : SSet.{0}) (M : ModuleCat.{0} R)
    (n : ℕ) (c : ((Basic.simplicialCochains K M).sc n).X₁) :
    cocycleHomologyEvaluation K M n (Representatives.cochainBoundaryMap (Basic.simplicialCochains K M) n c) = 0 := by
  ext h
  obtain ⟨z, rfl⟩ := ChainRepresentatives.chainClass_surjective (ChainDual.simplicialScalarChains (R := R) K) n h
  change evaluateCocycle K M n (Representatives.cochainBoundaryMap (Basic.simplicialCochains K M) n c)
    (ChainRepresentatives.chainClass (ChainDual.simplicialScalarChains (R := R) K) n z) = 0
  rw [evaluateCocycle_chainClass]
  exact coboundary_evaluation_cycle K M _ n c z

/-- Actual simplicial cohomology evaluates linearly on actual simplicial homology. -/
def simplicialHomologyEvaluation (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ) :
    (Basic.simplicialCochains K M).homology n →ₗ[R]
      ((ChainDual.simplicialScalarChains (R := R) K).homology n →ₗ[R] M) :=
  ((Representatives.cochainBoundaries (Basic.simplicialCochains K M) n).liftQ
    (cocycleHomologyEvaluation K M n)
    (by
      intro c hc
      rcases hc with ⟨w, rfl⟩
      exact cocycleHomologyEvaluation_boundary K M n w)).comp
    (Representatives.cohomologyQuotientIso (Basic.simplicialCochains K M) n).toLinearEquiv.toLinearMap

/-- The descended pairing is the original chain/cochain evaluation on representatives. -/
@[simp]
theorem simplicialHomologyEvaluation_class_class (K : SSet.{0}) (M : ModuleCat.{0} R)
    (n : ℕ) (c : Representatives.cochainCocycles (Basic.simplicialCochains K M) n)
    (z : ChainRepresentatives.chainCycles (ChainDual.simplicialScalarChains (R := R) K) n) :
    simplicialHomologyEvaluation K M n (Representatives.cochainClass (Basic.simplicialCochains K M) n c)
      (ChainRepresentatives.chainClass (ChainDual.simplicialScalarChains (R := R) K) n z) =
      ChainDual.degreewiseChainDualEquiv K M n (c : (Basic.simplicialCochains K M).X n)
        (z : (ChainDual.simplicialScalarChains (R := R) K).X n) := by
  dsimp only [simplicialHomologyEvaluation, Representatives.cochainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact evaluateCocycle_chainClass K M n c z

/-- Evaluation of singular cohomology with module coefficients on scalar singular homology. -/
def singularEvaluation (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    Basic.singularCohomology M X n →ₗ[R]
      ((singularScalarChains (R := R) X).homology n →ₗ[R] M) :=
  simplicialHomologyEvaluation (TopCat.toSSet.obj X) M n

/-- Singular evaluation is ordinary evaluation of an actual cocycle on an actual cycle. -/
@[simp]
theorem singularEvaluation_class_class (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ)
    (c : Representatives.singularCocycles M X n) (z : ChainRepresentatives.chainCycles (singularScalarChains (R := R) X) n) :
    singularEvaluation M X n (Representatives.singularClass M X n c)
      (ChainRepresentatives.chainClass (singularScalarChains (R := R) X) n z) =
      ChainDual.singularDegreewiseChainDualEquiv M X n (c : (Basic.singularCochains M X).X n)
        (z : (singularScalarChains (R := R) X).X n) :=
  simplicialHomologyEvaluation_class_class (TopCat.toSSet.obj X) M n c z

end

end OAI.AlgebraicTopology.Cohomology.Singular.Evaluation
