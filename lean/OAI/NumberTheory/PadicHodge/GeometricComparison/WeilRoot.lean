import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

/-! # Weil Root -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WeilRoot.WeilRootTransport

noncomputable section

/-! Transfer of the Weil bound from eigenvalue conjugates to every complex polynomial root. -/

variable (L : Type*) [Field L] [CharZero L] [IsAlgClosed L]

theorem complex_roots_of_conjugate_bounds (P : Polynomial ℚ) (hP : P ≠ 0) (r : ℝ)
    (h : ∀ α : L, Polynomial.aeval α P = 0 →
      ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ α) = 0 → ‖z‖ = r)
    (z : ℂ) (hz : Polynomial.aeval z P = 0) : ‖z‖ = r := by
  have hzint : IsIntegral ℚ z := IsAlgebraic.isIntegral ⟨P, hP, hz⟩
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero L (minpoly ℚ z)
    (ne_of_gt (minpoly.degree_pos hzint))
  have hαP : Polynomial.aeval α P = 0 :=
    Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero (minpoly.dvd ℚ z hz) hα
  have he : minpoly ℚ z = minpoly ℚ α :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hzint) hα (minpoly.monic hzint)
  apply h α hαP z
  rw [← he]
  exact minpoly.aeval ℚ z

theorem complex_roots_of_eigenvalue_bounds
    {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (T : Module.End L V) (P : Polynomial ℚ)
    (hP : T.charpoly = P.map (algebraMap ℚ L)) (r : ℝ)
    (h : ∀ α : L, T.HasEigenvalue α → IsAlgebraic ℚ α ∧
      ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ α) = 0 → ‖z‖ = r)
    (z : ℂ) (hz : Polynomial.aeval z P = 0) : ‖z‖ = r := by
  have hP0 : P ≠ 0 := by
    intro hzero
    exact (LinearMap.charpoly_monic T).ne_zero (by simpa only [hzero, Polynomial.map_zero] using hP)
  apply complex_roots_of_conjugate_bounds L P hP0 r (fun α hα => ?_) z hz
  apply (h α ?_).2
  apply (Module.End.hasEigenvalue_iff_isRoot_charpoly T α).mpr
  change T.charpoly.eval α = 0
  rw [hP, Polynomial.eval_map_algebraMap]
  exact hα

theorem integral_complex_roots_of_eigenvalue_bounds
    {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (T : Module.End L V) (P : Polynomial ℤ)
    (hP : T.charpoly = P.map (Int.castRingHom L)) (r : ℝ)
    (h : ∀ α : L, T.HasEigenvalue α → IsAlgebraic ℚ α ∧
      ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ α) = 0 → ‖z‖ = r)
    (z : ℂ) (hz : Polynomial.aeval z P = 0) : ‖z‖ = r := by
  apply complex_roots_of_eigenvalue_bounds L T (P.map (Int.castRingHom ℚ)) ?_ r h z ?_
  · rw [Polynomial.map_map]
    rw [show (algebraMap ℚ L).comp (Int.castRingHom ℚ) = Int.castRingHom L from
      Subsingleton.elim _ _]
    exact hP
  · rw [← Polynomial.aeval_eq_aeval_map
      (show (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = algebraMap ℤ ℂ from Subsingleton.elim _ _)]
    exact hz

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WeilRoot.WeilRootTransport
