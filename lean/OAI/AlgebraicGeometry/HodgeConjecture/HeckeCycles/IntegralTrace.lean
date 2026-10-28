import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm

/-! # Integral Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralTrace.CM

noncomputable section

/-! Turn CongruenceLevel's integer-valued rational trace form into the actual integral
bilinear map required by ReferenceFamily. Nondegeneracy on the full lattice follows
from rational nondegeneracy and its spanning property. -/

open scoped Classical
open OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def integralRestriction (B : LinearMap.BilinForm ℚ V) (Λ : Submodule ℤ V)
    (hint : ∀ x y : Λ, ∃ n : ℤ, B x.val y.val = (n : ℚ)) :
    LinearMap.BilinForm ℤ Λ := by
  let value := fun x y : Λ => (hint x y).choose
  have hv : ∀ x y : Λ, (value x y : ℚ) = B x.val y.val :=
    fun x y => (hint x y).choose_spec.symm
  refine {
    toFun := fun x => {
      toFun := value x
      map_add' := ?_
      map_smul' := ?_ }
    map_add' := ?_
    map_smul' := ?_ }
  · intro y z
    apply Int.cast_injective (α := ℚ)
    simp only [Int.cast_add, hv, Submodule.coe_add, map_add]
  · intro a y
    apply Int.cast_injective (α := ℚ)
    simp only [RingHom.id_apply, hv, Submodule.coe_smul,
      map_zsmul, smul_eq_mul, Int.cast_mul]
    exact zsmul_eq_mul _ _
  · intro x y
    apply LinearMap.ext
    intro z
    apply Int.cast_injective (α := ℚ)
    simp only [LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.add_apply, Int.cast_add, hv, Submodule.coe_add, map_add]
  · intro a x
    apply LinearMap.ext
    intro y
    apply Int.cast_injective (α := ℚ)
    simp only [LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.smul_apply, RingHom.id_apply, hv, Submodule.coe_smul,
      map_zsmul, smul_eq_mul, Int.cast_mul]
    exact zsmul_eq_mul _ _

theorem integralRestriction_cast (B : LinearMap.BilinForm ℚ V) (Λ : Submodule ℤ V)
    (hint : ∀ x y : Λ, ∃ n : ℤ, B x.val y.val = (n : ℚ)) (x y : Λ) :
    (integralRestriction B Λ hint x y : ℚ) = B x.val y.val :=
  (hint x y).choose_spec.symm

theorem integralRestriction_isAlt (B : LinearMap.BilinForm ℚ V) (Λ : Submodule ℤ V)
    (hint : ∀ x y : Λ, ∃ n : ℤ, B x.val y.val = (n : ℚ)) (hB : B.IsAlt) :
    (integralRestriction B Λ hint).IsAlt := by
  intro x
  apply Int.cast_injective (α := ℚ)
  rw [integralRestriction_cast, hB x.val, Int.cast_zero]

theorem integralRestriction_left_nondegenerate
    (B : LinearMap.BilinForm ℚ V) (Λ : Submodule ℤ V)
    (hint : ∀ x y : Λ, ∃ n : ℤ, B x.val y.val = (n : ℚ))
    (hfull : Submodule.span ℚ (Λ : Set V) = ⊤)
    (hB : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∀ x : Λ, (∀ y, integralRestriction B Λ hint x y = 0) → x = 0 := by
  intro x hx
  apply Subtype.ext
  apply hB x.val
  have hker : Submodule.span ℚ (Λ : Set V) ≤ LinearMap.ker (B x.val) := by
    apply Submodule.span_le.mpr
    intro y hy
    have h := congrArg (fun n : ℤ => (n : ℚ)) (hx ⟨y, hy⟩)
    change B x.val y = 0
    simpa only [integralRestriction_cast, Int.cast_zero] using h
  rw [hfull] at hker
  intro y
  exact hker (Submodule.mem_top : y ∈ (⊤ : Submodule ℚ V))

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]

/-- The rank-three trace form is the sum of the actual one-dimensional
CM trace pairings in the three coordinates. -/
def rationalTraceForm (b δ : E) (m : ℕ) : LinearMap.BilinForm ℚ (GeometricSource.CM.Vec E) :=
  (m : ℚ) • ∑ i : Fin 3,
    (ComplexMultiplication.CM.TraceForm.cmTracePairing E (δ * (if i = 2 then b else 1))).flip.compl₁₂
      (LinearMap.proj i) (LinearMap.proj i)

theorem rationalTraceForm_apply (b δ : E) (m : ℕ) (x y : GeometricSource.CM.Vec E) :
    rationalTraceForm E b δ m x y =
      (m : ℚ) * Algebra.trace ℚ E (δ * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y) := by
  change (m : ℚ) * (∑ i : Fin 3, Algebra.trace ℚ E
    ((δ * (if i = 2 then b else 1)) * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (y i) * x i)) = _
  simp only [NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  change δ * (if i = 2 then b else 1) *
    NumberField.IsCMField.complexConj E (y i) * x i =
      δ * ((if i = 2 then b else 1) * x i * NumberField.IsCMField.complexConj E (y i))
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralTrace.CM
