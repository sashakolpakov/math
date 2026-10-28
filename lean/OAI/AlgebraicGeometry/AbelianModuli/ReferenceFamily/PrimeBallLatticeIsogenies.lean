import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RationalBallNeighborhood
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClearedLatticeIsogenies

/-! # Prime Ball Lattice Isogenies -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PrimeBallLatticeIsogenies

noncomputable section

/-! Rational ball approximation can avoid every prime in an additional
positive integer. The actual two lattice maps have common square
multiplier, preserve the prescribed full marking, and meet the original
ball neighborhood. Thus polarization primes are controlled as well as
the level primes when these maps are algebraized. -/

theorem principal_lattice_map_of_multiple
    {L : Type*} [AddCommGroup L] (q : L →+ L) {N m : ℕ} (hNm : N ∣ m)
    (h : ∀ x, ∃ y, q x - x = m • y) : ∀ x, ∃ y, q x - x = N • y := by
  obtain ⟨d, rfl⟩ := hNm
  intro x
  obtain ⟨y, hy⟩ := h x
  exact ⟨d • y, hy.trans (mul_smul N d y)⟩

theorem exists_original_ball_paired_lattice_maps
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hHerm : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i))
    (hdet : H.det ≠ 0)
    (Λ : Submodule ℤ (Fin 3 → E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)
    (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ))
    (he : ∀ x y, Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y)
    (N C : ℕ) (hN : 0 < N) (hC : 0 < C) (z w : P.Domain)
    (U : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) (hU : IsOpen U) (hwU : w.val ∈ U) :
    ∃ (g : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) (D : ℕ) (q v : Λ →ₗ[ℤ] Λ),
      (∀ x y, Datum.RankThreePELDatum.matrixHermitian H (g x) (g y) =
        Datum.RankThreePELDatum.matrixHermitian H x y) ∧
      LinearMap.det g.toLinearMap = 1 ∧ P.lineActionVia e g z.val ∈ U ∧
      0 < D ∧ Nat.Coprime (D ^ 2) N ∧ Nat.Coprime (D ^ 2) C ∧ Nat.ModEq N (D ^ 2) 1 ∧
      (∀ x : Λ, (q x : Fin 3 → E) = D • g x) ∧
      (∀ x : Λ, (v x : Fin 3 → E) = D • g.symm x) ∧
      q.comp v = (D ^ 2 : ℤ) • (LinearMap.id : Λ →ₗ[ℤ] Λ) ∧
      v.comp q = (D ^ 2 : ℤ) • (LinearMap.id : Λ →ₗ[ℤ] Λ) ∧
      (∀ x : Λ, ∃ y : Λ, q x - x = N • y) ∧
      (∀ x : Λ, ∃ y : Λ, v x - x = N • y) := by
  obtain ⟨g, hg, hdetg, hc, hhit⟩ := RationalBallNeighborhood.exists_rational_isometry_in_original_ball_neighborhood
    P hP H hHerm hdet Λ hΛ e he (N * C) (Nat.mul_pos hN hC) z w U hU hwU
  obtain ⟨D, q, v, hD, hcop, hmod, hq, hv, hqv, hvq, hqN, hvN⟩ :=
    ClearedLatticeIsogenies.exists_paired_principal_lattice_maps Λ g hc
  have hNL : N ∣ N * C := ⟨C, rfl⟩
  have hCL : C ∣ N * C := ⟨N, Nat.mul_comm N C⟩
  have hDN : Nat.Coprime D N := Nat.Coprime.of_dvd_right hNL hcop
  have hDC : Nat.Coprime D C := Nat.Coprime.of_dvd_right hCL hcop
  exact ⟨g, D, q, v, hg, hdetg, hhit, hD, hDN.pow_left 2, hDC.pow_left 2,
    Nat.ModEq.of_dvd hNL hmod, hq, hv, hqv, hvq,
    principal_lattice_map_of_multiple q.toAddMonoidHom hNL hqN,
    principal_lattice_map_of_multiple v.toAddMonoidHom hNL hvN⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PrimeBallLatticeIsogenies
