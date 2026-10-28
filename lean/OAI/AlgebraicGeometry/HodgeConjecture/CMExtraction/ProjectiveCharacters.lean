import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DegreeZero
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveInvariants

/-! # Projective Characters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveCharacters.Local

noncomputable section

/-! Full GL3 characters with the same actual SL3 restriction have the
same projective normalized triple. Only three concrete determinant-zero
operators are needed; a general Satake isomorphism is not assumed. -/

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)
  {F : Type*} [Field F] [Algebra ℚ F]

theorem gl3_character_invariants (χ ψ : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) →ₐ[ℚ] F)
    (he : ∀ S : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q, χ (Retraction.Local.sl3ToGL3Hecke q v S) = ψ (Retraction.Local.sl3ToGL3Hecke q v S)) :
    χ (Minuscule.Local.gl3MinusculeHecke q 1) ^ 3 * χ (Degree.Local.gl3CentralUnit q).inv =
        ψ (Minuscule.Local.gl3MinusculeHecke q 1) ^ 3 * ψ (Degree.Local.gl3CentralUnit q).inv ∧
    χ (Minuscule.Local.gl3MinusculeHecke q 2) ^ 3 * χ (Degree.Local.gl3CentralUnit q).inv ^ 2 =
        ψ (Minuscule.Local.gl3MinusculeHecke q 2) ^ 3 * ψ (Degree.Local.gl3CentralUnit q).inv ^ 2 ∧
    χ (Minuscule.Local.gl3MinusculeHecke q 1) * χ (Minuscule.Local.gl3MinusculeHecke q 2) * χ (Degree.Local.gl3CentralUnit q).inv =
        ψ (Minuscule.Local.gl3MinusculeHecke q 1) * ψ (Minuscule.Local.gl3MinusculeHecke q 2) * ψ (Degree.Local.gl3CentralUnit q).inv := by
  obtain ⟨⟨S, hS⟩, ⟨T, hT⟩, ⟨U, hU⟩⟩ := DegreeZero.Local.gl3_minuscule_invariants_from_sl3 q v
  have hs := he S
  have ht := he T
  have hu := he U
  rw [hS, map_mul, map_pow, map_mul, map_pow] at hs
  rw [hT, map_mul, map_pow, map_pow, map_mul, map_pow, map_pow] at ht
  rw [hU, map_mul, map_mul, map_mul, map_mul] at hu
  exact ⟨hs, ht, hu⟩

theorem gl3_projective_triples [CharZero F] [IsAlgClosed F]
    (χ ψ : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) →ₐ[ℚ] F)
    (he : ∀ S : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q, χ (Retraction.Local.sl3ToGL3Hecke q v S) = ψ (Retraction.Local.sl3ToGL3Hecke q v S))
    (α β : Fin 3 → F)
    (hα : χ (Minuscule.Local.gl3MinusculeHecke q 1) = (q : F) * (α 0 + α 1 + α 2) ∧
      χ (Minuscule.Local.gl3MinusculeHecke q 2) = (q : F) * (α 0 * α 1 + α 0 * α 2 + α 1 * α 2) ∧
      χ (Minuscule.Local.gl3MinusculeHecke q 3) = α 0 * α 1 * α 2)
    (hβ : ψ (Minuscule.Local.gl3MinusculeHecke q 1) = (q : F) * (β 0 + β 1 + β 2) ∧
      ψ (Minuscule.Local.gl3MinusculeHecke q 2) = (q : F) * (β 0 * β 1 + β 0 * β 2 + β 1 * β 2) ∧
      ψ (Minuscule.Local.gl3MinusculeHecke q 3) = β 0 * β 1 * β 2) :
    ∃ c : F, c ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3), ∀ i, α i = c * β (σ i) := by
  have hQ : (q : F) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have ha : α 0 * α 1 * α 2 ≠ 0 := by
    rw [← hα.2.2, ← Degree.Local.gl3CentralUnit_val]
    exact ((Degree.Local.gl3CentralUnit q).isUnit.map χ).ne_zero
  have hb : β 0 * β 1 * β 2 ≠ 0 := by
    rw [← hβ.2.2, ← Degree.Local.gl3CentralUnit_val]
    exact ((Degree.Local.gl3CentralUnit q).isUnit.map ψ).ne_zero
  have hiχ : χ (Degree.Local.gl3CentralUnit q).inv = (α 0 * α 1 * α 2)⁻¹ := by
    change χ (↑((Degree.Local.gl3CentralUnit q)⁻¹) : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) = _
    rw [map_units_inv]
    rw [Degree.Local.gl3CentralUnit_val, hα.2.2]
  have hiψ : ψ (Degree.Local.gl3CentralUnit q).inv = (β 0 * β 1 * β 2)⁻¹ := by
    change ψ (↑((Degree.Local.gl3CentralUnit q)⁻¹) : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) = _
    rw [map_units_inv]
    rw [Degree.Local.gl3CentralUnit_val, hβ.2.2]
  obtain ⟨hs, hp, hm⟩ := gl3_character_invariants q v χ ψ he
  rw [hα.1, hβ.1, hiχ, hiψ] at hs
  rw [hα.2.1, hβ.2.1, hiχ, hiψ] at hp
  rw [hα.1, hα.2.1, hβ.1, hβ.2.1, hiχ, hiψ] at hm
  apply ProjectiveInvariants.Central.projective_triple_of_invariants α β ha hb
  · have hs' := (div_eq_div_iff ha hb).mp (show
        ((q : F) * (α 0 + α 1 + α 2)) ^ 3 / (α 0 * α 1 * α 2) =
        ((q : F) * (β 0 + β 1 + β 2)) ^ 3 / (β 0 * β 1 * β 2) by
          simpa only [div_eq_mul_inv] using hs)
    apply mul_left_cancel₀ (pow_ne_zero 3 hQ)
    convert hs' using 1 <;> ring
  · have hp' := (div_eq_div_iff (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)).mp (show
        ((q : F) * (α 0 * α 1 + α 0 * α 2 + α 1 * α 2)) ^ 3 / (α 0 * α 1 * α 2) ^ 2 =
        ((q : F) * (β 0 * β 1 + β 0 * β 2 + β 1 * β 2)) ^ 3 / (β 0 * β 1 * β 2) ^ 2 by
          simpa only [div_eq_mul_inv, inv_pow] using hp)
    apply mul_left_cancel₀ (pow_ne_zero 3 hQ)
    convert hp' using 1 <;> ring
  · have hm' := (div_eq_div_iff ha hb).mp (show
        ((q : F) * (α 0 + α 1 + α 2) * ((q : F) * (α 0 * α 1 + α 0 * α 2 + α 1 * α 2))) /
            (α 0 * α 1 * α 2) =
        ((q : F) * (β 0 + β 1 + β 2) * ((q : F) * (β 0 * β 1 + β 0 * β 2 + β 1 * β 2))) /
            (β 0 * β 1 * β 2) by simpa only [div_eq_mul_inv] using hm)
    apply mul_left_cancel₀ (pow_ne_zero 2 hQ)
    convert hm' using 1 <;> ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveCharacters.Local
