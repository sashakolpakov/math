/-
Discussions and model prompting: Alexander Kolpakov (UATX).

Source: sashakolpakov/spherical-regge-scissors, commit
d40eb8990bcf1ba5525435f8517e9ba5c202b549.
-/

import Mathlib

/-!
# The monomial phase action

The Regge formula becomes `a ↦ τ / a` after exponentiation.  Everything in
this file is proved in an arbitrary commutative group, so in particular it
applies to the unit group of every commutative field.  This is the precise
algebraic content of "acts monomially" needed by the manuscript.
-/

namespace SphericalReggeScissors

section CommGroup

variable {G : Type*} [CommGroup G]

/-- Four invertible moving phases and their common half-sum phase. -/
structure PhasePoint (G : Type*) [CommGroup G] where
  a : G
  b : G
  c : G
  d : G
  tau : G
  phase_relation : tau ^ 2 = a * b * c * d

/-- One coordinate of the monomial Regge action. -/
def reggePhase (tau u : G) : G := tau / u

@[simp]
theorem reggePhase_involutive (tau u : G) :
    reggePhase tau (reggePhase tau u) = u := by
  simp [reggePhase]

/-- The four transformed moving phases again have product `τ²`. -/
theorem reggePhase_product {a b c d tau : G}
    (h : tau ^ 2 = a * b * c * d) :
    tau ^ 2 = reggePhase tau a * reggePhase tau b *
      reggePhase tau c * reggePhase tau d := by
  simp only [reggePhase, div_eq_mul_inv]
  symm
  calc
    tau * a⁻¹ * (tau * b⁻¹) * (tau * c⁻¹) * (tau * d⁻¹) =
        tau ^ 4 * (a * b * c * d)⁻¹ := by
          simp only [pow_succ, pow_zero, mul_inv_rev]
          ac_rfl
    _ = tau ^ 4 * (tau ^ 2)⁻¹ := by rw [← h]
    _ = tau ^ 2 := by group

/-- The monomial Regge transformation on the phase hypersurface. -/
def PhasePoint.regge (z : PhasePoint G) : PhasePoint G where
  a := reggePhase z.tau z.a
  b := reggePhase z.tau z.b
  c := reggePhase z.tau z.c
  d := reggePhase z.tau z.d
  tau := z.tau
  phase_relation := reggePhase_product z.phase_relation

@[simp] theorem PhasePoint.regge_a (z : PhasePoint G) : z.regge.a = reggePhase z.tau z.a := rfl
@[simp] theorem PhasePoint.regge_b (z : PhasePoint G) : z.regge.b = reggePhase z.tau z.b := rfl
@[simp] theorem PhasePoint.regge_c (z : PhasePoint G) : z.regge.c = reggePhase z.tau z.c := rfl
@[simp] theorem PhasePoint.regge_d (z : PhasePoint G) : z.regge.d = reggePhase z.tau z.d := rfl
@[simp] theorem PhasePoint.regge_tau (z : PhasePoint G) : z.regge.tau = z.tau := rfl

/-- The phase transformation is an involution, including its defining relation. -/
theorem PhasePoint.regge_involutive (z : PhasePoint G) : z.regge.regge = z := by
  cases z
  simp [PhasePoint.regge]

end CommGroup

section Field

variable {K : Type*} [Field K]

/-- The Laurent expression which recovers a cosine Gram entry from a phase. -/
def gramEntry (u : K) : K := -(u + u⁻¹) / 2

/-- The elementary Laurent product-to-sum identity used in the determinant proof. -/
theorem phase_product_to_sum {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) :
    2 * ((u + u⁻¹) / 2) * ((v + v⁻¹) / 2) =
      ((u * v + (u * v)⁻¹) / 2) + ((u / v + (u / v)⁻¹) / 2) := by
  field_simp
  ring

@[simp]
theorem gramEntry_inv (u : K) : gramEntry u⁻¹ = gramEntry u := by
  simp [gramEntry, add_comm]

end Field

end SphericalReggeScissors
