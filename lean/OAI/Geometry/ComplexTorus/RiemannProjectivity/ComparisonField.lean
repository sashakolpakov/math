import OAI.Geometry.ComplexTorus.RiemannProjectivity.RationalLoops
import OAI.Geometry.ComplexTorus.RiemannProjectivity.PeriodsOn

/-! # Comparison Field -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.ComparisonField.Constructions.FieldComparison

/-! # RiemannProjectivity: the trace comparison with actual rational torus cohomology -/

open _root_.CategoryTheory
open scoped _root_.NumberField

variable {E : Type} [Field E] [NumberField E] [aE : Algebra ℚ E]
  [NumberField.IsCMField E] (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)

def integerPeriodMap : 𝓞 E →ₗ[ℤ] Φ.periodIntegerLattice where
  toFun a := ⟨Φ.periodEmbedding (a : E), (Φ.mem_periodIntegerLattice _).mpr ⟨a, rfl⟩⟩
  map_add' a b := by
    apply Subtype.ext
    change Φ.periodEmbedding ((a : E) + (b : E)) = _
    exact map_add Φ.periodEmbedding _ _
  map_smul' n a := by
    apply Subtype.ext
    change Φ.periodEmbedding (n • (a : E)) = n • Φ.periodEmbedding (a : E)
    exact map_zsmul Φ.periodEmbedding n (a : E)

def integerPeriodEquiv : 𝓞 E ≃ₗ[ℤ] Φ.periodIntegerLattice :=
  LinearEquiv.ofBijective (integerPeriodMap Φ) (by
    constructor
    · intro a b h
      apply Subtype.ext
      exact Φ.periodEmbedding.injective (congrArg Subtype.val h)
    · intro t
      obtain ⟨a, ha⟩ := (Φ.mem_periodIntegerLattice t).mp t.property
      exact ⟨a, Subtype.ext ha⟩)

omit [NumberField.IsCMField E] in
def integerDualRestriction : Module.Dual ℚ E →ₗ[ℚ] (𝓞 E →ₗ[ℤ] ℚ) where
  toFun f :=
    { toFun a := f (a : E)
      map_add' a b := f.map_add a b
      map_smul' n a := map_zsmul f n (a : E) }
  map_add' f g := by ext a; rfl
  map_smul' q f := by ext a; rfl

omit [NumberField.IsCMField E] in
theorem integerDualRestriction_bijective :
    Function.Bijective (integerDualRestriction (E := E)) := by
  have ha : aE = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  cases ha
  constructor
  · intro f g h
    apply (NumberField.integralBasis E).ext
    intro i
    rw [NumberField.integralBasis_apply]
    exact LinearMap.congr_fun h (NumberField.RingOfIntegers.basis E i)
  · intro χ
    let f := (NumberField.integralBasis E).constr ℚ
      (fun i => χ (NumberField.RingOfIntegers.basis E i))
    refine ⟨f, ?_⟩
    apply (NumberField.RingOfIntegers.basis E).ext
    intro i
    change f (algebraMap (𝓞 E) E (NumberField.RingOfIntegers.basis E i)) = _
    rw [← NumberField.integralBasis_apply]
    exact (NumberField.integralBasis E).constr_basis ℚ _ i

omit [NumberField.IsCMField E] in
def integerDualEquiv : Module.Dual ℚ E ≃ₗ[ℚ] (𝓞 E →ₗ[ℤ] ℚ) :=
  LinearEquiv.ofBijective integerDualRestriction integerDualRestriction_bijective

def latticeCharacterEquiv : (𝓞 E →ₗ[ℤ] ℚ) ≃ₗ[ℚ] (Φ.periodIntegerLattice →ₗ[ℤ] ℚ) where
  toFun χ := χ.comp (integerPeriodEquiv Φ).symm.toLinearMap
  invFun χ := χ.comp (integerPeriodEquiv Φ).toLinearMap
  left_inv χ := by ext a; simp
  right_inv χ := by ext a; simp
  map_add' χ ψ := by ext a; rfl
  map_smul' q χ := by ext a; rfl

/-- Trace, the integral lattice, and actual loop evaluation define the rational comparison. -/
def fieldBettiEquiv : E ≃ₗ[ℚ]
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Φ.periodTorus) 1 :=
  (PeriodsOn.Constructions.Periods.traceDualEquiv E).trans
    (integerDualEquiv.trans ((latticeCharacterEquiv Φ).trans (RationalLoops.Constructions.Characters.rationalPeriodEquiv Φ).symm))

theorem fieldBettiEquiv_period (x : E) (a : 𝓞 E) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of Φ.periodTorus) 1
      (fieldBettiEquiv Φ x) (RationalLoops.Constructions.Loops.latticeHomology Φ ℚ (integerPeriodEquiv Φ a)) =
        Algebra.trace ℚ E (x * (a : E)) := by
  have h := (RationalLoops.Constructions.Characters.rationalPeriodEquiv Φ).apply_symm_apply
    (latticeCharacterEquiv Φ (integerDualEquiv (PeriodsOn.Constructions.Periods.traceDualEquiv E x)))
  have hp := LinearMap.congr_fun h (integerPeriodEquiv Φ a)
  change _ = PeriodsOn.Constructions.Periods.traceDualEquiv E x ((integerPeriodEquiv Φ).symm (integerPeriodEquiv Φ a) : E)
    at hp
  simpa only [LinearEquiv.symm_apply_apply, PeriodsOn.Constructions.Periods.traceDualEquiv_apply] using! hp

/-- The invariant covector of the rational class has the expected trace periods. -/
theorem fieldBettiEquiv_covector (x : E) (a : 𝓞 E) :
    RationalLoops.Constructions.Characters.rationalCovector Φ (fieldBettiEquiv Φ x) (Φ.periodEmbedding (a : E)) =
      (Algebra.trace ℚ E (x * (a : E)) : ℂ) := by
  have h := RationalLoops.Constructions.Characters.rationalCovector_period Φ (fieldBettiEquiv Φ x) (integerPeriodEquiv Φ a)
  rw [fieldBettiEquiv_period] at h
  exact h

end Geometry.ComplexTorus.RiemannProjectivity.ComparisonField.Constructions.FieldComparison

namespace Geometry.ComplexTorus.RiemannProjectivity.ComparisonField.Constructions.HodgeComparison

/-!
# RiemannProjectivity: the prescribed Hodge signs under the canonical torus comparison

The complexified trace comparison is determined by its actual lattice
periods. On the positive embedding summand these are precisely the periods
of the complex-linear covector already constructed from the CM type.
-/

open _root_.CategoryTheory
open scoped _root_.NumberField TensorProduct

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)

def fieldComplexCovectorEquiv : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E ≃ₗ[ℂ] (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) :=
  (LinearEquiv.baseChange ℚ ℂ _ _ (FieldComparison.fieldBettiEquiv Φ)).trans
    (RationalLoops.Constructions.Rational.rationalComplexificationCovectors Φ)

theorem fieldComplexCovectorEquiv_tmul (c : ℂ) (x : E) :
    fieldComplexCovectorEquiv Φ (c ⊗ₜ[ℚ] x) =
      c • RationalLoops.Constructions.Characters.rationalCovector Φ (FieldComparison.fieldBettiEquiv Φ x) := by
  change (BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ).symm
    (c • AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of Φ.periodTorus) 1
      (FieldComparison.fieldBettiEquiv Φ x)) = _
  exact (BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ).symm.map_smul c _

theorem fieldComplexCovectorEquiv_period (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) (a : 𝓞 E) :
    fieldComplexCovectorEquiv Φ x (Φ.periodEmbedding (a : E)) =
      (Algebra.traceForm ℚ E).baseChange ℂ x (1 ⊗ₜ[ℚ] (a : E)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, add_apply, LinearMap.add_apply, hx, hy]
  | tmul c x =>
    rw [fieldComplexCovectorEquiv_tmul, smul_apply,
      FieldComparison.fieldBettiEquiv_covector, LinearMap.BilinForm.baseChange_tmul,
      Algebra.traceForm_apply]
    change c * (Algebra.trace ℚ E (x * (a : E)) : ℂ) =
      (Algebra.trace ℚ E (x * (a : E)) : ℂ) * (c * 1)
    ring

/-- Equality of the actual covectors, not merely agreement of abstract dimensions. -/
theorem fieldComplexCovectorEquiv_holomorphic (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E)
    (hx : x ∈ Φ.hodgeStructure.holomorphic) :
    fieldComplexCovectorEquiv Φ x =
      (PeriodsOn.Constructions.Periods.periodCovector E Φ x).toContinuousLinearMap.restrictScalars ℝ := by
  let l := (PeriodsOn.Constructions.Periods.periodCovector E Φ x).toContinuousLinearMap.restrictScalars ℝ
  let χ : Φ.periodIntegerLattice →+ ℂ :=
    l.toLinearMap.toAddMonoidHom.comp Φ.periodIntegerLattice.subtype.toAddMonoidHom
  have hl : ∀ t : Φ.periodIntegerLattice, l t = χ t := fun _ => rfl
  have hc : ∀ t : Φ.periodIntegerLattice, fieldComplexCovectorEquiv Φ x t = χ t := by
    intro t
    obtain ⟨a, ha⟩ := (Φ.mem_periodIntegerLattice t).mp t.property
    change fieldComplexCovectorEquiv Φ x t.val = PeriodsOn.Constructions.Periods.periodCovector E Φ x t.val
    rw [← ha, fieldComplexCovectorEquiv_period, PeriodsOn.Constructions.Periods.periodCovector_on_field E Φ x hx]
  exact (PrimitiveEq.Constructions.Primitive.exists_covector_extending_character Φ.periodIntegerLattice χ).unique hc hl

/-- Conversely, a complex-linear covector determines a unique positive embedding vector. -/
theorem fieldComplexCovectorEquiv_complexLinear_iff (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) :
    (∃ l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℂ] ℂ, fieldComplexCovectorEquiv Φ x = l.restrictScalars ℝ) ↔
      x ∈ Φ.hodgeStructure.holomorphic := by
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨y, hy⟩ := (PeriodsOn.Constructions.Periods.holomorphicPeriodEquiv E Φ).surjective l.toLinearMap
    have hxy : fieldComplexCovectorEquiv Φ x = fieldComplexCovectorEquiv Φ y.val := by
      rw [hl, fieldComplexCovectorEquiv_holomorphic Φ y.val y.property]
      have he : PeriodsOn.Constructions.Periods.periodCovector E Φ y.val = l.toLinearMap := hy
      rw [he]
      rfl
    exact (fieldComplexCovectorEquiv Φ).injective hxy ▸ y.property
  · intro hx
    exact ⟨(PeriodsOn.Constructions.Periods.periodCovector E Φ x).toContinuousLinearMap,
      fieldComplexCovectorEquiv_holomorphic Φ x hx⟩

end Geometry.ComplexTorus.RiemannProjectivity.ComparisonField.Constructions.HodgeComparison

end

end OAI
