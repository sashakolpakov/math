import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PositiveMinusculeValues
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CentralMinuscule

/-! # Minuscule Values -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.MinusculeValues.Iwasawa

noncomputable section

/-! The original raw minuscule operators evaluate at the inverse torus
coordinates. The result follows from proved positive minuscule integrals
and exact central-translation identities in the actual Hecke algebra. -/

variable (q : ℕ) [Fact q.Prime]

theorem gl3TorusSatakeOver_central_inverse (t : Fin 3 → ℂˣ) :
    TorusCharacters.Iwasawa.gl3TorusSatakeOver q t (Degree.Local.gl3CentralUnit q).inv = (t 0 : ℂ) * (t 1 : ℂ) * (t 2 : ℂ) := by
  change TorusCharacters.Iwasawa.gl3TorusSatakeOver q t (↑((Degree.Local.gl3CentralUnit q)⁻¹) : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) = _
  rw [map_units_inv, Degree.Local.gl3CentralUnit_val, TorusCharacters.Iwasawa.gl3TorusSatakeOver_central, inv_inv]

theorem gl3TorusSatakeOver_first (t : Fin 3 → ℂˣ) :
    TorusCharacters.Iwasawa.gl3TorusSatakeOver q t (Minuscule.Local.gl3MinusculeHecke q 1) =
      (q : ℂ) * ((t 0 : ℂ)⁻¹ + (t 1 : ℂ)⁻¹ + (t 2 : ℂ)⁻¹) := by
  have h := congrArg (TorusCharacters.Iwasawa.gl3TorusSatakeOver q t) (CentralMinuscule.Iwasawa.gl3_central_inverse_first q)
  rw [map_mul, gl3TorusSatakeOver_central_inverse, PositiveMinusculeValues.Iwasawa.gl3Torus_positive_second] at h
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (t 0).ne_zero (t 1).ne_zero) (t 2).ne_zero)
  rw [h]
  field_simp
  ring

theorem gl3TorusSatakeOver_second (t : Fin 3 → ℂˣ) :
    TorusCharacters.Iwasawa.gl3TorusSatakeOver q t (Minuscule.Local.gl3MinusculeHecke q 2) =
      (q : ℂ) * ((t 0 : ℂ)⁻¹ * (t 1 : ℂ)⁻¹ + (t 0 : ℂ)⁻¹ * (t 2 : ℂ)⁻¹ +
        (t 1 : ℂ)⁻¹ * (t 2 : ℂ)⁻¹) := by
  have h := congrArg (TorusCharacters.Iwasawa.gl3TorusSatakeOver q t) (CentralMinuscule.Iwasawa.gl3_central_inverse_second q)
  rw [map_mul, gl3TorusSatakeOver_central_inverse, PositiveMinusculeValues.Iwasawa.gl3Torus_positive_first] at h
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (t 0).ne_zero (t 1).ne_zero) (t 2).ne_zero)
  rw [h]
  field_simp
  ring

theorem gl3TorusSatakeOver_map {F L : Type*} [Field F] [Field L] [Algebra ℚ F] [Algebra ℚ L]
    (j : F →ₐ[ℚ] L) (t : Fin 3 → Fˣ) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
    j (TorusCharacters.Iwasawa.gl3TorusSatakeOver q t T) = TorusCharacters.Iwasawa.gl3TorusSatakeOver q (fun i => Units.map j.toMonoidHom (t i)) T :=
  SatakeBaseChange.Iwasawa.rationalLatticeEvaluation_map j t (Satake.Iwasawa.gl3RationalSatake q T)

theorem gl3TorusSatakeOver_minuscule_over {F : Type*} [Field F] [Algebra ℚ F]
    (j : F →ₐ[ℚ] ℂ) (t : Fin 3 → Fˣ) :
    TorusCharacters.Iwasawa.gl3TorusSatakeOver q t (Minuscule.Local.gl3MinusculeHecke q 1) =
        (q : F) * ((t 0 : F)⁻¹ + (t 1 : F)⁻¹ + (t 2 : F)⁻¹) ∧
    TorusCharacters.Iwasawa.gl3TorusSatakeOver q t (Minuscule.Local.gl3MinusculeHecke q 2) =
        (q : F) * ((t 0 : F)⁻¹ * (t 1 : F)⁻¹ + (t 0 : F)⁻¹ * (t 2 : F)⁻¹ +
          (t 1 : F)⁻¹ * (t 2 : F)⁻¹) ∧
    TorusCharacters.Iwasawa.gl3TorusSatakeOver q t (Minuscule.Local.gl3MinusculeHecke q 3) =
        (t 0 : F)⁻¹ * (t 1 : F)⁻¹ * (t 2 : F)⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · apply j.injective
    change j (TorusCharacters.Iwasawa.gl3TorusSatakeOver q t (Minuscule.Local.gl3MinusculeHecke q 1)) = _
    rw [gl3TorusSatakeOver_map, gl3TorusSatakeOver_first]
    simp
  · apply j.injective
    change j (TorusCharacters.Iwasawa.gl3TorusSatakeOver q t (Minuscule.Local.gl3MinusculeHecke q 2)) = _
    rw [gl3TorusSatakeOver_map, gl3TorusSatakeOver_second]
    simp
  · rw [TorusCharacters.Iwasawa.gl3TorusSatakeOver_central]
    simp only [mul_inv_rev]
    ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.MinusculeValues.Iwasawa
