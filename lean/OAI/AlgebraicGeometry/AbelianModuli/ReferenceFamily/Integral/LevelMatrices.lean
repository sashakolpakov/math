import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDenominators

/-! # Level Matrices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.LevelMatrices

noncomputable section

/-! Deep congruences on the specified integral lattice become integral
matrix congruences in the standard E-coordinates, after one fixed
nonzero denominator is cleared. -/

open scoped Classical

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]

omit [Algebra ℚ E] in
theorem lattice_congruence_coordinates (Λ : Submodule ℤ (Fin 3 → E))
    (d c : ℤ) (hd : d ≠ 0)
    (hbasis : ∀ j : Fin 3, d • (Pi.single j (1 : E)) ∈ Λ)
    (hcoords : ∀ y ∈ Λ, ∀ i, IsIntegral ℤ (c • y i))
    (N m : ℕ) (k : ℤ) (hN : (N : ℤ) = d * c * m * k)
    (g : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E))
    (hg : ∀ x ∈ Λ, ∃ y ∈ Λ, g x - x = (N : ℤ) • y)
    (i j : Fin 3) :
    ∃ a : E, IsIntegral ℤ a ∧
      (LinearMap.toMatrix' g.toLinearMap) i j - (1 : Matrix (Fin 3) (Fin 3) E) i j = (m : E) * a := by
  obtain ⟨y, hy, he⟩ := hg (d • Pi.single j 1) (hbasis j)
  have hgsmul : g (d • Pi.single j 1) = d • g (Pi.single j 1) :=
    (g.toLinearMap.restrictScalars ℤ).map_smul d _
  have he' : d • (g (Pi.single j 1) - Pi.single j 1) = (N : ℤ) • y := by
    rw [smul_sub, ← hgsmul]
    exact he
  have hz := congrArg (fun x : Fin 3 → E => x i) he'
  have hz' : (d : E) * (g (Pi.single j 1) i - (Pi.single j 1 : Fin 3 → E) i) =
      (N : E) * y i := by
    simpa only [Pi.sub_apply, Pi.smul_apply, zsmul_eq_mul, Int.cast_natCast] using hz
  refine ⟨k • (c • y i), (hcoords y hy i).smul k, ?_⟩
  change g (Pi.single j 1) i - (1 : Matrix (Fin 3) (Fin 3) E) i j = _
  have hid : (1 : Matrix (Fin 3) (Fin 3) E) i j = (Pi.single j 1 : Fin 3 → E) i := by
    simp only [Matrix.one_apply, Pi.single_apply]
  rw [hid]
  apply mul_left_cancel₀ (show (d : E) ≠ 0 from Int.cast_ne_zero.mpr hd)
  rw [hz']
  have hc : (N : E) = (d : E) * (c : E) * (m : E) * (k : E) := by exact_mod_cast hN
  rw [hc]
  simp only [zsmul_eq_mul]
  ring

/-- Every prescribed coefficient modulus admits a fixed principal
level whose matrices are congruent to identity over the ring of integers. -/
theorem exists_integral_matrix_congruence_depth (Λ : Submodule ℤ (Fin 3 → E))
    (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set (Fin 3 → E)) = ⊤)
    (m : ℕ) (hm : 0 < m) :
    ∃ D : ℕ, 0 < D ∧ ∀ N : ℕ, D ∣ N →
      ∀ g : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E),
        (∀ x ∈ Λ, ∃ y ∈ Λ, g x - x = (N : ℤ) • y) →
        ∀ i j, ∃ a : E, IsIntegral ℤ a ∧
          (LinearMap.toMatrix' g.toLinearMap) i j -
            (1 : Matrix (Fin 3) (Fin 3) E) i j = (m : E) * a := by
  obtain ⟨d, hd, hbasis⟩ := LatticeDenominators.common_integer_multiple_mem Λ hspan (fun j : Fin 3 => Pi.single j (1 : E))
  obtain ⟨c, hc, hcoords⟩ := LatticeDenominators.common_integral_coordinate_multiple Λ hfg
  refine ⟨(d * c * (m : ℤ)).natAbs, Int.natAbs_pos.mpr
    (mul_ne_zero (mul_ne_zero hd hc) (by exact_mod_cast hm.ne')), ?_⟩
  intro N hN g hg i j
  have hdiv : d * c * (m : ℤ) ∣ (N : ℤ) := Int.natAbs_dvd_natAbs.mp (by
    simpa only [Int.natAbs_natCast] using hN)
  obtain ⟨k, hk⟩ := hdiv
  exact lattice_congruence_coordinates Λ d c hd hbasis hcoords N m k hk g hg i j

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.LevelMatrices
