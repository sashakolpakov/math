import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.CMField

/-! # Weight One -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM

noncomputable section

/-!
# Rational weight-one Hodge structures and rank-one CM actions

Complexification here is the actual tensor product `ℂ ⊗[ℚ] U`.
Conjugation acts on its complex coefficient, and a rational Hodge map is
tested using its canonical scalar extension. These definitions implement
the linear-algebraic hypotheses in the manuscript's main theorem.
-/

open scoped TensorProduct

variable (U : Type*) [AddCommGroup U] [Module ℚ U]

/-- Complexification of a rational vector space. -/
abbrev Complexification := ℂ ⊗[ℚ] U

/-- Complex conjugation acts on the coefficient factor, fixing rational vectors. -/
def coefficientConjugation : Complexification U →ₗ[ℚ] Complexification U :=
  TensorProduct.map (Complex.conjAe.restrictScalars ℚ).toLinearMap LinearMap.id

@[simp]
theorem coefficientConjugation_tmul (z : ℂ) (u : U) :
    coefficientConjugation U (z ⊗ₜ[ℚ] u) = star z ⊗ₜ[ℚ] u := rfl

@[simp]
theorem coefficientConjugation_involutive (x : Complexification U) :
    coefficientConjugation U (coefficientConjugation U x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul z u => simp
  | add x y hx hy => simp [hx, hy]

/-- A finite-dimensional rational Hodge structure of weight one, with the
actual direct-sum and conjugation conditions on its complexification. -/
structure WeightOneHodgeStructure where
  [finiteDimensional : FiniteDimensional ℚ U]
  holomorphic : Submodule ℂ (Complexification U)
  antiholomorphic : Submodule ℂ (Complexification U)
  complementary : IsCompl holomorphic antiholomorphic
  conjugate_mem : ∀ x, coefficientConjugation U x ∈ antiholomorphic ↔ x ∈ holomorphic

variable {U}
variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

theorem baseChange_coefficientConjugation (f : U →ₗ[ℚ] V) (x : Complexification U) :
    f.baseChange ℂ (coefficientConjugation U x) =
      coefficientConjugation V (f.baseChange ℂ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z u => simp
  | add x y hx hy => simp [hx, hy]

/-- A rational map preserves Hodge type when its actual complexification
preserves the holomorphic subspace. Conjugation forces preservation of the other type. -/
def IsHodgeMap (H : WeightOneHodgeStructure U) (K : WeightOneHodgeStructure V)
    (f : U →ₗ[ℚ] V) : Prop :=
  ∀ x ∈ H.holomorphic, f.baseChange ℂ x ∈ K.holomorphic

theorem IsHodgeMap.map_antiholomorphic {H : WeightOneHodgeStructure U}
    {K : WeightOneHodgeStructure V} {f : U →ₗ[ℚ] V} (h : IsHodgeMap H K f)
    {x : Complexification U} (hx : x ∈ H.antiholomorphic) :
    f.baseChange ℂ x ∈ K.antiholomorphic := by
  have hx' : coefficientConjugation U x ∈ H.holomorphic :=
    (H.conjugate_mem _).mp (by simpa using hx)
  have hf := (K.conjugate_mem _).mpr (h _ hx')
  simpa [baseChange_coefficientConjugation] using hf

theorem isHodgeMap_id (H : WeightOneHodgeStructure U) :
    IsHodgeMap H H LinearMap.id := by
  intro x hx
  simpa using hx

theorem IsHodgeMap.comp {H : WeightOneHodgeStructure U}
    {K : WeightOneHodgeStructure V} {L : WeightOneHodgeStructure W}
    {f : U →ₗ[ℚ] V} {g : V →ₗ[ℚ] W}
    (hg : IsHodgeMap K L g) (hf : IsHodgeMap H K f) :
    IsHodgeMap H L (g.comp f) := by
  intro x hx
  simpa [LinearMap.baseChange_comp] using hg _ (hf _ hx)

variable (E : Type*) [Field E] [Algebra ℚ E] [Module E U] [IsScalarTower ℚ E U]

/-- Multiplication by a field element as a rational linear endomorphism. -/
def scalarEndomorphism (a : E) : U →ₗ[ℚ] U where
  toFun := fun u => a • u
  map_add' := smul_add a
  map_smul' := fun q u => smul_comm a q u

/-- The rank-one CM hypothesis uses the standard number-field and CM-field
predicates, an actual compatible field action, and preservation of Hodge type.
It has no hypothesis concerning algebraic cycles. -/
structure RankOneCMAction (H : WeightOneHodgeStructure U) : Prop where
  [numberField : NumberField E]
  [cmField : NumberField.IsCMField E]
  rank_one : Module.finrank E U = 1
  hodge_action : ∀ a : E, IsHodgeMap H H (scalarEndomorphism E a)

variable {E}

/-- A rank-one CM summand has rational dimension equal to the field degree. -/
theorem RankOneCMAction.rational_finrank {H : WeightOneHodgeStructure U}
    (h : RankOneCMAction E H) : Module.finrank ℚ U = Module.finrank ℚ E := by
  simpa [h.rank_one] using (Module.finrank_mul_finrank ℚ E U).symm

/-- The rank-one condition gives an actual linear equivalence with the CM field. -/
def RankOneCMAction.equivField {H : WeightOneHodgeStructure U}
    (h : RankOneCMAction E H) : U ≃ₗ[E] E := by
  letI : FiniteDimensional ℚ U := H.finiteDimensional
  letI : FiniteDimensional E U := Module.Finite.of_restrictScalars_finite ℚ E U
  exact LinearEquiv.ofFinrankEq U E (by simpa using h.rank_one)

/-- The specified CM field acts faithfully; it cannot be replaced by a zero action. -/
theorem RankOneCMAction.scalarEndomorphism_injective {H : WeightOneHodgeStructure U}
    (h : RankOneCMAction E H) : Function.Injective (scalarEndomorphism (U := U) E) := by
  intro a b hab
  let e := h.equivField
  have heq := congrArg (fun f : U →ₗ[ℚ] U => e (f (e.symm 1))) hab
  simpa [scalarEndomorphism] using heq

end

end OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM
