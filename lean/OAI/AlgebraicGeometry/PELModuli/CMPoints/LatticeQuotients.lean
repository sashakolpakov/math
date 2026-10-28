import OAI.AlgebraicGeometry.PELModuli.CMPoints.LatticeComparison
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarCoordinates

/-! # Lattice Quotients -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.LatticeQuotients

noncomputable section

/-! A full O_E-stable lattice in E^3 becomes a free rank-three module
modulo all powers of every sufficiently large prime. The bound and
equivalences are constructed by clearing actual lattice denominators. -/

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)

theorem exists_lattice_quotient_bound :
    ∃ D : ℕ, 0 < D ∧ ∀ q : ℕ, q.Prime → D < q → ∀ n : ℕ,
      Nonempty (ScalarQuotientMk.ScalarQuotient (NumberField.RingOfIntegers E) (LatticeComparison.stableIntegerLattice Λ hΛ)
        (q ^ n) ≃ₗ[NumberField.RingOfIntegers E]
        (Fin 3 → NumberField.RingOfIntegers E ⧸
          Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E)))) := by
  obtain ⟨c, hc, f, g, hgf, hfg⟩ := LatticeComparison.exists_integral_lattice_comparison Λ hΛ
  have hcpos : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  refine ⟨c.natAbs, hcpos, fun q hq hbound n => ?_⟩
  have hcop := hq.coprime_pow_of_not_dvd (m := n)
    (show ¬ q ∣ c.natAbs from fun hd => (not_le_of_gt hbound) (Nat.le_of_dvd hcpos hd))
  have hicop : IsCoprime c (q ^ n : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by
      simpa only [Int.gcd_def, Int.natAbs_pow, Int.natAbs_natCast] using hcop)
  have hcopE : IsCoprime (c : NumberField.RingOfIntegers E)
      (q ^ n : NumberField.RingOfIntegers E) := by
    have h := hicop.map (Int.castRingHom (NumberField.RingOfIntegers E))
    change IsCoprime (c : NumberField.RingOfIntegers E)
      ((q ^ n : ℤ) : NumberField.RingOfIntegers E) at h
    simpa only [Int.cast_pow, Int.cast_natCast] using h
  let e := ScalarQuotientMk.scalarQuotientEquiv (q ^ n : NumberField.RingOfIntegers E)
    (c : NumberField.RingOfIntegers E) hcopE f g
    (fun x => (hgf x).trans (Int.cast_smul_eq_zsmul _ c x).symm)
    (fun x => (hfg x).trans (Int.cast_smul_eq_zsmul _ c x).symm)
  exact ⟨e.symm.trans (ScalarCoordinates.scalarCoordinateEquiv _)⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.LatticeQuotients
