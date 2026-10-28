import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadial

/-! # Dual Radial Satake -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadialSatake.Iwasawa

noncomputable section

section

/-! The native inverse-transpose character is defined over the same
algebraic closure and complex embedding as its dilation root. -/

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters.ParameterChoices
open scoped Classical TensorProduct

variable (q : ℕ) [Fact q.Prime]

theorem sqrtUnit_sq : (SatakeParameters.Iwasawa.sqrtUnit q : ℂ) ^ 2 = (q : ℂ) := by
  change (Real.sqrt (q : ℝ) : ℂ) ^ 2 = (q : ℂ)
  norm_cast
  exact Real.sq_sqrt (Nat.cast_nonneg _)

theorem sqrtUnit_algebraic : IsAlgebraic ℚ (SatakeParameters.Iwasawa.sqrtUnit q : ℂ) := by
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  rw [sqrtUnit_sq]
  exact isAlgebraic_natCast q

def algebraicSqrt (j : ParameterChoices.Qbar →+* ℂ) : ParameterChoices.Qbar :=
  Parameters.ParameterChoices.liftComplexAlgebraic j (SatakeParameters.Iwasawa.sqrtUnit q : ℂ) (sqrtUnit_algebraic q)

theorem algebraicSqrt_image (j : ParameterChoices.Qbar →+* ℂ) : j (algebraicSqrt q j) = (SatakeParameters.Iwasawa.sqrtUnit q : ℂ) :=
  Parameters.ParameterChoices.liftComplexAlgebraic_image j _ _

theorem algebraicSqrt_sq (j : ParameterChoices.Qbar →+* ℂ) : (algebraicSqrt q j) ^ 2 = (q : ParameterChoices.Qbar) :=
  j.injective (by rw [map_pow, algebraicSqrt_image, sqrtUnit_sq, map_natCast])

theorem algebraicSqrt_ne_zero (j : ParameterChoices.Qbar →+* ℂ) : algebraicSqrt q j ≠ 0 := by
  intro hz
  have h := algebraicSqrt_image q j
  rw [hz, map_zero] at h
  exact (SatakeParameters.Iwasawa.sqrtUnit q).ne_zero h.symm

def algebraicSqrtUnit (j : ParameterChoices.Qbar →+* ℂ) : ParameterChoices.Qbarˣ := Units.mk0 _ (algebraicSqrt_ne_zero q j)

theorem algebraicSqrtUnit_image (j : ParameterChoices.Qbar →+* ℂ) :
    Units.map j.toMonoidHom (algebraicSqrtUnit q j) = SatakeParameters.Iwasawa.sqrtUnit q :=
  Units.ext (algebraicSqrt_image q j)

def algebraicDualTorusPoint (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbarˣ) : Fin 3 → ParameterChoices.Qbarˣ :=
  ![algebraicSqrtUnit q j, (algebraicSqrtUnit q j)⁻¹, a⁻¹]

theorem algebraicDualTorusPoint_image (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbarˣ) :
    (fun i => Units.map j.toMonoidHom (algebraicDualTorusPoint q j a i)) =
      DualSatakeParameters.Iwasawa.dualRadialTorusPoint q (Units.map j.toMonoidHom a) := by
  funext i
  fin_cases i
  · exact algebraicSqrtUnit_image q j
  · exact (map_inv (Units.map j.toMonoidHom) _).trans (congrArg Inv.inv (algebraicSqrtUnit_image q j))
  · exact map_inv (Units.map j.toMonoidHom) a

def algebraicDualSatakeCharacter (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbarˣ) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →ₐ[ℚ] ParameterChoices.Qbar := SatakeBaseChange.Iwasawa.torusSatakeOver q (algebraicDualTorusPoint q j a)

theorem algebraicDualSatakeCharacter_image (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbarˣ)
    (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    j (algebraicDualSatakeCharacter q j a T) =
      DualRadial.Iwasawa.dualRadialSatakeCharacter q (Units.map j.toMonoidHom a) ((1 : ℂ) ⊗ₜ[ℚ] T) := by
  change j.toRatAlgHom (SatakeBaseChange.Iwasawa.torusSatakeOver q (algebraicDualTorusPoint q j a) T) = _
  rw [SatakeBaseChange.Iwasawa.torusSatakeOver_map]
  change SatakeBaseChange.Iwasawa.torusSatakeOver q (fun i => Units.map j.toMonoidHom (algebraicDualTorusPoint q j a i)) T = _
  rw [algebraicDualTorusPoint_image q j a, SatakeBaseChange.Iwasawa.torusSatakeOver_complex]
  rfl

theorem algebraicDualSatakeCharacter_conjugate (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbarˣ)
    (σ : Gal(ParameterChoices.Qbar/ℚ)) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    σ (algebraicDualSatakeCharacter q j a T) =
      SatakeBaseChange.Iwasawa.torusSatakeOver q (fun i => Units.map σ.toMonoidHom (algebraicDualTorusPoint q j a i)) T :=
  SatakeBaseChange.Iwasawa.torusSatakeOver_map q σ.toAlgHom _ T

end

/-! The inverse-transpose radial character over the same chosen algebraic closure,
with the complex image fixed by the original embedding. -/

open scoped Classical TensorProduct _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters.ParameterChoices

variable (q : ℕ) [Fact q.Prime]

def algebraicDualRadialTorusPoint (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbarˣ) : Fin 3 → ParameterChoices.Qbarˣ :=
  ![algebraicSqrtUnit q j, (algebraicSqrtUnit q j)⁻¹, a⁻¹]

theorem algebraicDualRadialTorusPoint_image (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbarˣ) :
    (fun i => Units.map j.toMonoidHom (algebraicDualRadialTorusPoint q j a i)) =
      DualSatakeParameters.Iwasawa.dualRadialTorusPoint q (Units.map j.toMonoidHom a) := by
  funext i
  fin_cases i
  · exact algebraicSqrtUnit_image q j
  · exact (map_inv (Units.map j.toMonoidHom) _).trans
      (congrArg Inv.inv (algebraicSqrtUnit_image q j))
  · exact map_inv (Units.map j.toMonoidHom) a

def algebraicDualRadialSatakeCharacter (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbarˣ) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →ₐ[ℚ] ParameterChoices.Qbar :=
  SatakeBaseChange.Iwasawa.torusSatakeOver q (algebraicDualRadialTorusPoint q j a)

theorem algebraicDualRadialSatakeCharacter_image (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbarˣ)
    (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    j (algebraicDualRadialSatakeCharacter q j a T) =
      DualRadial.Iwasawa.dualRadialSatakeCharacter q (Units.map j.toMonoidHom a) (1 ⊗ₜ[ℚ] T) := by
  change j.toRatAlgHom (SatakeBaseChange.Iwasawa.torusSatakeOver q (algebraicDualRadialTorusPoint q j a) T) = _
  rw [SatakeBaseChange.Iwasawa.torusSatakeOver_map]
  change SatakeBaseChange.Iwasawa.torusSatakeOver q (fun i => Units.map j.toMonoidHom (algebraicDualRadialTorusPoint q j a i)) T = _
  rw [algebraicDualRadialTorusPoint_image, SatakeBaseChange.Iwasawa.torusSatakeOver_complex]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadialSatake.Iwasawa
