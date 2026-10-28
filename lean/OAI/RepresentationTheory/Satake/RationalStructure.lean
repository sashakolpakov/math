import Mathlib

/-! # Rational Structure -/

namespace OAI.RepresentationTheory.Satake.RationalStructure.Construction

noncomputable section

/-!
# RationalStructure: rational structure of normalized Satake

The definitions and final theorem type reproduce `Statements/RationalStructure.lean` in
an independent namespace, so no statement stub is imported. The rational
unnormalized coefficient formula and the specified cocharacter lattice are
the mathematical inputs. The concrete convolution algebra and its geometric
realization remain outside this coefficient-level formulation.
-/

abbrev AmbientCocharacters (s : ℕ) :=
  (Fin s → Fin 3 → ℤ) × ℤ

def rhoPairing {s : ℕ}
    {L : AddSubgroup (AmbientCocharacters s)} (l : L) : ℤ :=
  ∑ v : Fin s, (l.val.1 v 0 - l.val.1 v 2)

def extendQ {I : Type*} (f : I →₀ ℚ) : I →₀ ℂ :=
  f.mapRange (algebraMap ℚ ℂ) (map_zero (algebraMap ℚ ℂ))

def conjugateCoefficients {I : Type*}
    (σ : ℂ ≃ₐ[ℚ] ℂ) (f : I →₀ ℂ) : I →₀ ℂ :=
  f.mapRange σ (map_zero σ)

def IsSatakeParameter
    {D L : Type*} [AddCommGroup L]
    (S : (D →₀ ℂ) →ₗ[ℂ] (L →₀ ℂ))
    (χ : D → ℂ) (z : L → ℂ) : Prop :=
  z 0 = 1 ∧
  (∀ l m, z (l + m) = z l * z m) ∧
  ∀ d, χ d =
    (S (Finsupp.single d 1)).sum (fun l c => c * z l)

@[simp] theorem extendQ_apply {I : Type*} (f : I →₀ ℚ) (i : I) :
    extendQ f i = (f i : ℂ) := rfl

@[simp] theorem extendQ_zero {I : Type*} :
    extendQ (0 : I →₀ ℚ) = 0 := by
  ext i
  simp

theorem extendQ_add {I : Type*} (f g : I →₀ ℚ) :
    extendQ (f + g) = extendQ f + extendQ g := by
  ext i
  simp

theorem extendQ_smul {I : Type*} (r : ℚ) (f : I →₀ ℚ) :
    extendQ (r • f) = (r : ℂ) • extendQ f := by
  ext i
  simp [Finsupp.smul_apply, smul_eq_mul]

@[simp] theorem extendQ_single {I : Type*} (i : I) (r : ℚ) :
    extendQ (Finsupp.single i r) = Finsupp.single i (r : ℂ) := by
  exact Finsupp.mapRange_single

@[simp] theorem conjugateCoefficients_apply {I : Type*}
    (σ : ℂ ≃ₐ[ℚ] ℂ) (f : I →₀ ℂ) (i : I) :
    conjugateCoefficients σ f i = σ (f i) := rfl

@[simp] theorem conjugateCoefficients_zero {I : Type*}
    (σ : ℂ ≃ₐ[ℚ] ℂ) :
    conjugateCoefficients σ (0 : I →₀ ℂ) = 0 := by
  ext i
  simp

theorem conjugateCoefficients_add {I : Type*}
    (σ : ℂ ≃ₐ[ℚ] ℂ) (f g : I →₀ ℂ) :
    conjugateCoefficients σ (f + g) =
      conjugateCoefficients σ f + conjugateCoefficients σ g := by
  ext i
  simp

theorem conjugateCoefficients_smul {I : Type*}
    (σ : ℂ ≃ₐ[ℚ] ℂ) (c : ℂ) (f : I →₀ ℂ) :
    conjugateCoefficients σ (c • f) =
      σ c • conjugateCoefficients σ f := by
  ext i
  simp [Finsupp.smul_apply, smul_eq_mul]

@[simp] theorem conjugateCoefficients_single {I : Type*}
    (σ : ℂ ≃ₐ[ℚ] ℂ) (i : I) (c : ℂ) :
    conjugateCoefficients σ (Finsupp.single i c) =
      Finsupp.single i (σ c) := by
  exact Finsupp.mapRange_single

@[simp] theorem conjugateCoefficients_extendQ {I : Type*}
    (σ : ℂ ≃ₐ[ℚ] ℂ) (f : I →₀ ℚ) :
    conjugateCoefficients σ (extendQ f) = extendQ f := by
  ext i
  simp

/-- Rational coefficients of a finitely supported vector have finite support. -/
theorem exists_rational_lift {I : Type*} (f : I →₀ ℂ) (c : I → ℚ)
    (hc : ∀ i, (c i : ℂ) = f i) :
    ∃ g : I →₀ ℚ, extendQ g = f := by
  classical
  have hsupport : ∀ i, c i ≠ 0 → i ∈ f.support := by
    intro i hi
    rw [Finsupp.mem_support_iff, ← hc i]
    exact_mod_cast hi
  refine ⟨Finsupp.onFinset f.support c hsupport, ?_⟩
  ext i
  exact hc i

theorem linear_map_single {D I : Type*}
    (S : (D →₀ ℂ) →ₗ[ℂ] (I →₀ ℂ)) (d : D) (c : ℂ) :
    S (Finsupp.single d c) = c • S (Finsupp.single d 1) := by
  calc
    S (Finsupp.single d c) = S (c • Finsupp.single d 1) := by
      simp
    _ = c • S (Finsupp.single d 1) := S.map_smul c _

/-- A rational image for every standard basis vector gives rational descent. -/
theorem rational_descent_of_basis {D I : Type*}
    (S : (D →₀ ℂ) →ₗ[ℂ] (I →₀ ℂ))
    (b : D → I →₀ ℚ)
    (hb : ∀ d, extendQ (b d) = S (Finsupp.single d 1)) :
    ∃ SQ : (D →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ),
      ∀ f, extendQ (SQ f) = S (extendQ f) := by
  refine ⟨Finsupp.linearCombination ℚ b, ?_⟩
  intro f
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [map_add, extendQ_add, hf, hg]
  | single d r =>
      rw [Finsupp.linearCombination_single, extendQ_smul, hb,
        extendQ_single, linear_map_single S d (r : ℂ)]

/-- A complex-linear map with rational basis images commutes with scalars. -/
theorem conjugation_of_rational_basis {D I : Type*}
    (S : (D →₀ ℂ) →ₗ[ℂ] (I →₀ ℂ))
    (b : D → I →₀ ℚ)
    (hb : ∀ d, extendQ (b d) = S (Finsupp.single d 1))
    (σ : ℂ ≃ₐ[ℚ] ℂ) (f : D →₀ ℂ) :
    S (conjugateCoefficients σ f) =
      conjugateCoefficients σ (S f) := by
  have hfixed (d : D) :
      conjugateCoefficients σ (S (Finsupp.single d 1)) =
        S (Finsupp.single d 1) := by
    rw [← hb d, conjugateCoefficients_extendQ]
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [conjugateCoefficients_add, map_add, hf, hg]
  | single d c =>
      rw [conjugateCoefficients_single, linear_map_single S d (σ c),
        linear_map_single S d c, conjugateCoefficients_smul, hfixed]

/-- Evaluating at a dual-torus point respects scalar conjugation. -/
theorem parameter_conjugation_of_rational_basis
    {D L : Type*} [AddCommGroup L]
    (S : (D →₀ ℂ) →ₗ[ℂ] (L →₀ ℂ))
    (b : D → L →₀ ℚ)
    (hb : ∀ d, extendQ (b d) = S (Finsupp.single d 1))
    (σ : ℂ ≃ₐ[ℚ] ℂ) (χ : D → ℂ) (z : L → ℂ)
    (hz : IsSatakeParameter S χ z) :
    IsSatakeParameter S (fun d => σ (χ d)) (fun l => σ (z l)) := by
  rcases hz with ⟨hz0, hzadd, hχ⟩
  refine ⟨?_, ?_, ?_⟩
  · dsimp only
    rw [hz0, map_one]
  · intro l m
    dsimp only
    rw [hzadd, map_mul]
  · intro d
    dsimp only
    rw [hχ d, map_finsuppSum]
    apply Finsupp.sum_congr
    intro l hl
    have hfixed : σ (S (Finsupp.single d 1) l) =
        S (Finsupp.single d 1) l := by
      rw [← hb d]
      simp
    rw [map_mul, hfixed]

/-- RationalStructure, with exactly the hypotheses and conclusion of the specification. -/
theorem normalized_satake_rational_structure
    (s : ℕ)
    (L : AddSubgroup (AmbientCocharacters s))
    (D : Type*)
    (q : ℕ) (_hq : q.Prime)
    (a : D → L → ℚ)
    (S : (D →₀ ℂ) →ₗ[ℂ] (L →₀ ℂ))
    (hformula : ∀ d l,
      S (Finsupp.single d 1) l =
        (q : ℂ) ^ rhoPairing l * (a d l : ℂ)) :
    (∃ SQ : (D →₀ ℚ) →ₗ[ℚ] (L →₀ ℚ),
      ∀ f, extendQ (SQ f) = S (extendQ f)) ∧
    (∀ (σ : ℂ ≃ₐ[ℚ] ℂ) (f : D →₀ ℂ),
      S (conjugateCoefficients σ f) =
        conjugateCoefficients σ (S f)) ∧
    (∀ (σ : ℂ ≃ₐ[ℚ] ℂ) (χ : D → ℂ) (z : L → ℂ),
      IsSatakeParameter S χ z →
        IsSatakeParameter S
          (fun d => σ (χ d))
          (fun l => σ (z l))) := by
  classical
  have hlift (d : D) :
      ∃ g : L →₀ ℚ, extendQ g = S (Finsupp.single d 1) := by
    apply exists_rational_lift (S (Finsupp.single d 1))
      (fun l => (q : ℚ) ^ rhoPairing l * a d l)
    intro l
    simp [hformula, Rat.cast_mul, Rat.cast_zpow]
  choose b hb using hlift
  exact ⟨rational_descent_of_basis S b hb,
    conjugation_of_rational_basis S b hb,
    parameter_conjugation_of_rational_basis S b hb⟩

end

end OAI.RepresentationTheory.Satake.RationalStructure.Construction
