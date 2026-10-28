import OAI.AlgebraicTopology.Cohomology.Singular.ChainDual
import OAI.AlgebraicTopology.Cohomology.Singular.Representatives
import OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives
import OAI.AlgebraicTopology.Cohomology.Singular.Evaluation
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Universal Coefficient -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient

noncomputable section

/-!
# Universal coefficient duality over a field

The canonical singular cohomology evaluation map is an isomorphism over a field.
The linear algebra below uses extension of linear functionals, as proved in
mathlib by extending bases, with no finite-dimensionality assumption.
-/

open _root_.CategoryTheory

variable {F : Type} [Field F]

/-- A functional which vanishes on a linear map's kernel factors through that map.
No splitting or extension is an extra assumption: mathlib supplies it over a field. -/
theorem functionalFactors_of_vanishesOnKernel
    {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (f : V →ₗ[F] W) (φ : V →ₗ[F] F)
    (hφ : ∀ v : V, f v = 0 → φ v = 0) :
    ∃ ψ : W →ₗ[F] F, ψ.comp f = φ := by
  have hmem : φ ∈ (LinearMap.ker f).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    exact hφ
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker f] at hmem
  exact hmem

/-- A scalar cocycle which evaluates to zero on every cycle is a coboundary.
This uses the actual chain and cochain complexes in every degree, including zero. -/
theorem cochainClass_eq_zero_of_vanishesOnCycles (K : SSet.{0}) (n : ℕ)
    (c : Representatives.cochainCocycles (Basic.simplicialCochains K (ModuleCat.of F F)) n)
    (hc : ∀ z : ChainRepresentatives.chainCycles (ChainDual.simplicialScalarChains (R := F) K) n,
      ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n c.val z.val = 0) :
    Representatives.cochainClass (Basic.simplicialCochains K (ModuleCat.of F F)) n c = 0 := by
  let C := ChainDual.simplicialScalarChains (R := F) K
  let D := Basic.simplicialCochains K (ModuleCat.of F F)
  let φ : C.X n →ₗ[F] F := ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n c.val
  obtain ⟨ψ, hψ⟩ := functionalFactors_of_vanishesOnKernel (C.sc n).g.hom φ
    (fun z hz => hc ⟨z, hz⟩)
  let p : (D.sc n).X₁ :=
    (ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) ((ComplexShape.up ℕ).prev n)).symm ψ
  have hp : (D.sc n).f p = (c : D.X n) := by
    apply (ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n).injective
    change ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n
      (D.d ((ComplexShape.up ℕ).prev n) n p) = φ
    rw [ChainDual.degreewiseChainDualEquiv_d]
    have he : ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F)
        ((ComplexShape.up ℕ).prev n) p = ψ :=
      (ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F)
        ((ComplexShape.up ℕ).prev n)).apply_symm_apply ψ
    rw [he]
    exact hψ
  apply (Representatives.cochainClass_eq_zero_iff D n c).mpr
  exact ⟨p, Subtype.ext hp⟩

/-- Every functional on actual scalar homology is evaluation by a scalar cocycle.
The necessary extension from the cycle subspace is proved by mathlib's basis extension. -/
theorem exists_cocycle_realizing_homologyFunctional (K : SSet.{0}) (n : ℕ)
    (L : (ChainDual.simplicialScalarChains (R := F) K).homology n →ₗ[F] F) :
    ∃ c : Representatives.cochainCocycles (Basic.simplicialCochains K (ModuleCat.of F F)) n,
      ∀ z : ChainRepresentatives.chainCycles (ChainDual.simplicialScalarChains (R := F) K) n,
        ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n c.val z.val =
          L (ChainRepresentatives.chainClass (ChainDual.simplicialScalarChains (R := F) K) n z) := by
  let C := ChainDual.simplicialScalarChains (R := F) K
  let D := Basic.simplicialCochains K (ModuleCat.of F F)
  obtain ⟨φ, hφ⟩ := (L.comp (ChainRepresentatives.chainClass C n)).exists_extend
  let c : D.X n := (ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n).symm φ
  have hbound : φ.comp (C.sc n).f.hom = 0 := by
    ext z
    have hz := LinearMap.congr_fun hφ (ChainRepresentatives.chainBoundaryMap C n z)
    change φ ((C.sc n).f z) = L (ChainRepresentatives.chainClass C n (ChainRepresentatives.chainBoundaryMap C n z)) at hz
    rw [ChainRepresentatives.chainClass_boundary, map_zero] at hz
    change φ ((C.sc n).f z) = 0
    exact hz
  have hc : c ∈ Representatives.cochainCocycles D n := by
    change (D.d n ((ComplexShape.up ℕ).next n)) c = 0
    apply (ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) ((ComplexShape.up ℕ).next n)).injective
    rw [ChainDual.degreewiseChainDualEquiv_d, map_zero]
    have he : ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n c = φ :=
      (ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n).apply_symm_apply φ
    rw [he]
    exact hbound
  refine ⟨⟨c, hc⟩, fun z => ?_⟩
  have hz := LinearMap.congr_fun hφ z
  simpa only [c, LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
    Submodule.subtype_apply] using hz

/-- Over a field, two cohomology classes are equal whenever their canonical
evaluations on all homology classes agree. -/
theorem simplicialHomologyEvaluation_injective (K : SSet.{0}) (n : ℕ) :
    Function.Injective (Evaluation.simplicialHomologyEvaluation K (ModuleCat.of F F) n) := by
  intro a b hab
  let C := ChainDual.simplicialScalarChains (R := F) K
  let D := Basic.simplicialCochains K (ModuleCat.of F F)
  have hzero : Evaluation.simplicialHomologyEvaluation K (ModuleCat.of F F) n (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := Representatives.cochainClass_surjective D n (a - b)
  have hc0 : Representatives.cochainClass D n c = 0 := by
    apply cochainClass_eq_zero_of_vanishesOnCycles K n c
    intro z
    have hz : Evaluation.simplicialHomologyEvaluation K (ModuleCat.of F F) n
        (Representatives.cochainClass D n c) (ChainRepresentatives.chainClass C n z) = 0 := by
      rw [hc, hzero]
      rfl
    exact (Evaluation.simplicialHomologyEvaluation_class_class K (ModuleCat.of F F) n c z).symm.trans hz
  exact sub_eq_zero.mp (hc.symm.trans hc0)

/-- Every scalar-linear functional on homology is canonical evaluation by a
cohomology class when the coefficient ring is a field. -/
theorem simplicialHomologyEvaluation_surjective (K : SSet.{0}) (n : ℕ) :
    Function.Surjective (Evaluation.simplicialHomologyEvaluation K (ModuleCat.of F F) n) := by
  intro L
  obtain ⟨c, hc⟩ := exists_cocycle_realizing_homologyFunctional K n L
  refine ⟨Representatives.cochainClass (Basic.simplicialCochains K (ModuleCat.of F F)) n c, ?_⟩
  ext h
  obtain ⟨z, rfl⟩ := ChainRepresentatives.chainClass_surjective (ChainDual.simplicialScalarChains (R := F) K) n h
  rw [Evaluation.simplicialHomologyEvaluation_class_class]
  exact hc z

/-- The field universal-coefficient isomorphism for the actual simplicial chain
and cochain complexes, with the canonical evaluation map as its forward map. -/
def simplicialUniversalCoefficientEquiv (K : SSet.{0}) (n : ℕ) :
    (Basic.simplicialCochains K (ModuleCat.of F F)).homology n ≃ₗ[F]
      Module.Dual F ((ChainDual.simplicialScalarChains (R := F) K).homology n) :=
  LinearEquiv.ofBijective (Evaluation.simplicialHomologyEvaluation K (ModuleCat.of F F) n)
    ⟨simplicialHomologyEvaluation_injective K n,
      simplicialHomologyEvaluation_surjective K n⟩

@[simp]
theorem simplicialUniversalCoefficientEquiv_apply (K : SSet.{0}) (n : ℕ)
    (c : (Basic.simplicialCochains K (ModuleCat.of F F)).homology n) :
    simplicialUniversalCoefficientEquiv K n c =
      Evaluation.simplicialHomologyEvaluation K (ModuleCat.of F F) n c := rfl

/-- Canonical universal-coefficient duality for genuine singular cohomology and
homology over an arbitrary field, in every nonnegative degree. -/
def singularUniversalCoefficientEquiv (X : TopCat.{0}) (n : ℕ) :
    Basic.singularCohomology (ModuleCat.of F F) X n ≃ₗ[F]
      Module.Dual F ((Evaluation.singularScalarChains (R := F) X).homology n) :=
  simplicialUniversalCoefficientEquiv (TopCat.toSSet.obj X) n

@[simp]
theorem singularUniversalCoefficientEquiv_apply (X : TopCat.{0}) (n : ℕ)
    (c : Basic.singularCohomology (ModuleCat.of F F) X n) :
    singularUniversalCoefficientEquiv X n c =
      Evaluation.singularEvaluation (ModuleCat.of F F) X n c := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient
