import OAI.Analysis.DifferentialForms.Manifold.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! # Bidegree -/

namespace OAI.Analysis.DifferentialForms.Manifold.Bidegree

noncomputable section

/-!
Pure bidegree for actual complex-valued real alternating covectors.

The defining condition is the eigencharacter for pullback by multiplication
on a complex vector space. Its inverse-scalar formulation is the covector
action in the official Hodge statement. This file does not posit a Hodge
decomposition or any geometric comparison theorem.
-/

open scoped ContDiff

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- Simultaneous complex scalar pullback on all the real tangent arguments. -/
def scalarCovectorPullback (n : ℕ) (z : ℂ) :
    (E [⋀^Fin n]→L[ℝ] ℂ) →ₗ[ℂ] (E [⋀^Fin n]→L[ℝ] ℂ) where
  toFun form := form.compContinuousLinearMap (ContinuousLinearMap.lsmul ℝ ℂ z)
  map_add' form η := by ext v; rfl
  map_smul' c form := by ext v; rfl

@[simp]
theorem scalarCovectorPullback_apply (n : ℕ) (z : ℂ)
    (form : E [⋀^Fin n]→L[ℝ] ℂ) (v : Fin n → E) :
    scalarCovectorPullback E n z form v = form (fun i => z • v i) := rfl

@[simp]
theorem scalarCovectorPullback_one (n : ℕ) (form : E [⋀^Fin n]→L[ℝ] ℂ) :
    scalarCovectorPullback E n 1 form = form := by
  ext v
  simp

theorem scalarCovectorPullback_mul (n : ℕ) (z w : ℂ)
    (form : E [⋀^Fin n]→L[ℝ] ℂ) :
    scalarCovectorPullback E n (z * w) form =
      scalarCovectorPullback E n w (scalarCovectorPullback E n z form) := by
  ext v
  simp only [scalarCovectorPullback_apply, mul_smul]

/-- The direct pullback character for bidegree `(p,q)`. -/
def bidegreeCharacter (p q : ℕ) (z : ℂˣ) : ℂ :=
  (z : ℂ) ^ p * (star (z : ℂ)) ^ q

@[simp]
theorem bidegreeCharacter_one (p q : ℕ) : bidegreeCharacter p q 1 = 1 := by
  simp [bidegreeCharacter]

theorem bidegreeCharacter_mul (p q : ℕ) (z w : ℂˣ) :
    bidegreeCharacter p q (z * w) =
      bidegreeCharacter p q z * bidegreeCharacter p q w := by
  simp only [bidegreeCharacter, Units.val_mul, star_mul, mul_pow]
  ring

/-- Inverse scalar pullback has the negative powers in the official convention. -/
theorem bidegreeCharacter_inv (p q : ℕ) (z : ℂˣ) :
    bidegreeCharacter p q z⁻¹ =
      ((z : ℂ) ^ p)⁻¹ * ((star (z : ℂ)) ^ q)⁻¹ := by
  simp [bidegreeCharacter, inv_pow]

/-- A pure `(p,q)` covector, defined by the complex-scalar pullback character. -/
def HasBidegree (p q : ℕ) (form : E [⋀^Fin (p + q)]→L[ℝ] ℂ) : Prop :=
  ∀ (z : ℂˣ) (v : Fin (p + q) → E),
    form (fun i => (z : ℂ) • v i) = bidegreeCharacter p q z * form v

/-- Pure covectors form a complex-linear subspace of real alternating covectors. -/
def pureBidegreeSubmodule (p q : ℕ) :
    Submodule ℂ (E [⋀^Fin (p + q)]→L[ℝ] ℂ) where
  carrier := HasBidegree E p q
  zero_mem' := by intro z v; simp
  add_mem' := by
    intro form η hform hη z v
    change form (fun i => (z : ℂ) • v i) + η (fun i => (z : ℂ) • v i) =
      bidegreeCharacter p q z * (form v + η v)
    rw [hform z v, hη z v, mul_add]
  smul_mem' := by
    intro c form hform z v
    change c * form (fun i => (z : ℂ) • v i) =
      bidegreeCharacter p q z * (c * form v)
    rw [hform z v]
    ring

omit [IsScalarTower ℝ ℂ E] in
@[simp]
theorem mem_pureBidegreeSubmodule (p q : ℕ)
    (form : E [⋀^Fin (p + q)]→L[ℝ] ℂ) :
    form ∈ pureBidegreeSubmodule E p q ↔ HasBidegree E p q form := Iff.rfl

/-- Equivalence with the negative-character covector convention in the PDF. -/
theorem hasBidegree_iff_inverse_pullback (p q : ℕ)
    (form : E [⋀^Fin (p + q)]→L[ℝ] ℂ) :
    HasBidegree E p q form ↔ ∀ z : ℂˣ,
      scalarCovectorPullback E (p + q) (↑(z⁻¹) : ℂ) form =
        (((z : ℂ) ^ p)⁻¹ * ((star (z : ℂ)) ^ q)⁻¹) • form := by
  constructor
  · intro h z
    ext v
    simpa only [scalarCovectorPullback_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, bidegreeCharacter_inv] using h z⁻¹ v
  · intro h z v
    have hz := congrArg (fun η : E [⋀^Fin (p + q)]→L[ℝ] ℂ => η v) (h z⁻¹)
    simpa [scalarCovectorPullback_apply, bidegreeCharacter] using hz

omit [IsScalarTower ℝ ℂ E] in
/-- Every degree-zero alternating covector is of bidegree `(0,0)`. -/
theorem hasBidegree_zero (form : E [⋀^Fin (0 + 0)]→L[ℝ] ℂ) :
    HasBidegree E 0 0 form := by
  intro z v
  have hv : (fun i => (z : ℂ) • v i) = v := by
    funext i
    exact Fin.elim0 i
  simp [hv, bidegreeCharacter]

/-- A complex-linear functional viewed as a complex-valued real one-form. -/
def complexLinearCovector (f : E →L[ℂ] ℂ) : E [⋀^Fin 1]→L[ℝ] ℂ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1) (f.restrictScalars ℝ)

@[simp]
theorem complexLinearCovector_apply (f : E →L[ℂ] ℂ) (v : Fin 1 → E) :
    complexLinearCovector E f v = f (v 0) := rfl

/-- In particular, differentials of complex-linear coordinates have type `(1,0)`. -/
theorem complexLinearCovector_hasBidegree (f : E →L[ℂ] ℂ) :
    HasBidegree E 1 0 (complexLinearCovector E f) := by
  intro z v
  simp [bidegreeCharacter]

/-- The conjugate of a complex-linear coordinate functional. -/
def conjugateLinearCovector (f : E →L[ℂ] ℂ) : E [⋀^Fin 1]→L[ℝ] ℂ :=
  Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap
    (complexLinearCovector E f)

@[simp]
theorem conjugateLinearCovector_apply (f : E →L[ℂ] ℂ) (v : Fin 1 → E) :
    conjugateLinearCovector E f v = star (f (v 0)) := rfl

/-- Conjugate coordinate differentials have type `(0,1)`. -/
theorem conjugateLinearCovector_hasBidegree (f : E →L[ℂ] ℂ) :
    HasBidegree E 0 1 (conjugateLinearCovector E f) := by
  intro z v
  simp [bidegreeCharacter, star_mul, mul_comm]

omit [IsScalarTower ℝ ℂ E] in
/-- Smooth pure forms are precisely the smooth sections with pure values. -/
def pureSmoothFormSubmodule (p q : ℕ) : Submodule ℂ (Manifold.Basic.SmoothForm E (p + q)) :=
  ⨅ x : E, (pureBidegreeSubmodule E p q).comap (Manifold.Basic.SmoothForm.eval x)

omit [IsScalarTower ℝ ℂ E] in
@[simp]
theorem mem_pureSmoothFormSubmodule (p q : ℕ) (form : Manifold.Basic.SmoothForm E (p + q)) :
    form ∈ pureSmoothFormSubmodule E p q ↔ ∀ x : E, HasBidegree E p q (form x) := by
  simp [pureSmoothFormSubmodule]

omit [IsScalarTower ℝ ℂ E] in
/-- A smooth pure-type form, as an actual submodule of smooth real forms. -/
abbrev PureSmoothForm (p q : ℕ) := ↥(pureSmoothFormSubmodule E p q)

namespace PureSmoothForm

variable {E} {p q : ℕ}

omit [IsScalarTower ℝ ℂ E] in
instance : CoeFun (PureSmoothForm E p q) (fun _ => Manifold.Basic.RawForm E (p + q)) :=
  ⟨fun form => form.1⟩

omit [IsScalarTower ℝ ℂ E] in
theorem smooth (form : PureSmoothForm E p q) : ContDiff ℝ ∞ (form : Manifold.Basic.RawForm E (p + q)) :=
  form.1.smooth

omit [IsScalarTower ℝ ℂ E] in
theorem hasBidegree (form : PureSmoothForm E p q) (x : E) :
    HasBidegree E p q (form x) :=
  (mem_pureSmoothFormSubmodule E p q form.1).mp form.2 x

end PureSmoothForm

omit [IsScalarTower ℝ ℂ E] in
/-- Any pure covector defines a constant smooth pure form. -/
def constantPureSmoothForm (p q : ℕ) (form : pureBidegreeSubmodule E p q) :
    PureSmoothForm E p q :=
  ⟨Manifold.Basic.SmoothForm.ofSmooth (fun _ : E => form.1) contDiff_const,
    (mem_pureSmoothFormSubmodule E p q _).mpr (fun _ => form.2)⟩

omit [IsScalarTower ℝ ℂ E] in
@[simp]
theorem constantPureSmoothForm_apply (p q : ℕ) (form : pureBidegreeSubmodule E p q)
    (x : E) : constantPureSmoothForm E p q form x = form.1 := rfl

end

end OAI.Analysis.DifferentialForms.Manifold.Bidegree
