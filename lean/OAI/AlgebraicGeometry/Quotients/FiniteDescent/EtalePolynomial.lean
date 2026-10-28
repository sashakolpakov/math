import OAI.AlgebraicGeometry.Quotients.FiniteDescent.EtaleLocal
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesX
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesFin

/-! # Etale Polynomial -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.EtalePolynomial.Construction.EtalePolynomialFactorial

noncomputable section

/-! Factoriality of a local étale algebra over polynomial coordinates at a rational point. -/

variable {K S : Type*} [Field K] [Infinite K] [CommRing S] [Algebra K S]
variable [IsLocalRing S] [IsNoetherianRing S]

theorem of_point (n : ℕ) [Algebra (MvPolynomial (Fin n) K) S]
    [IsScalarTower K (MvPolynomial (Fin n) K) S]
    [Algebra.FormallyEtale (MvPolynomial (Fin n) K) S]
    [Algebra.EssFiniteType (MvPolynomial (Fin n) K) S]
    (e : S →ₐ[K] K) (he : RingHom.ker e = IsLocalRing.maximalIdeal S) :
    UniqueFactorizationMonoid S := by
  let P := MvPolynomial (Fin n) K
  let T := MvPowerSeries (Fin n) K
  let v : Fin n → K := fun i => e (algebraMap P S (MvPolynomial.X i))
  have hev (p : P) : e (algebraMap P S p) = MvPolynomial.eval v p := by
    have h : e.toRingHom.comp (algebraMap P S) = MvPolynomial.eval v := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, MvPolynomial.eval_C]
        change e (algebraMap P S (algebraMap K P c)) = c
        rw [← IsScalarTower.algebraMap_apply K P S]
        exact e.commutes c
      · intro i
        simp [v]
    exact RingHom.congr_fun h p
  let f : P →ₐ[K] T := PowerSeriesX.Construction.PowerSeriesFlatShift.map v
  let : Algebra P T := f.toAlgebra
  have : Module.Flat P T := PowerSeriesX.Construction.PowerSeriesFlatShift.flat v
  have : IsDomain T := NoZeroDivisors.to_isDomain _
  have : UniqueFactorizationMonoid T := PowerSeriesFin.Construction.PowerSeriesFactorial.fin K n
  have : IsAdicComplete (IsLocalRing.maximalIdeal T) T := PowerSeriesIs.Construction.PowerSeriesLocal.isAdicComplete
  let m := IsLocalRing.maximalIdeal T
  let q : S →ₐ[P] T ⧸ m := {
    toRingHom := ((Ideal.Quotient.mk m).comp MvPowerSeries.C).comp e.toRingHom
    commutes' := fun p => by
      change Ideal.Quotient.mk m (MvPowerSeries.C (e (algebraMap P S p))) =
        Ideal.Quotient.mk m (f p)
      rw [Ideal.Quotient.eq]
      apply (PowerSeriesIs.Construction.PowerSeriesLocal.mem_maximalIdeal_iff _).mpr
      rw [map_sub, MvPowerSeries.constantCoeff_C, PowerSeriesX.Construction.PowerSeriesFlatShift.constantCoeff_map, hev,
        sub_self] }
  apply EtaleLocal.Construction.EtaleLocalFactorial.of_residue_map q
  ext s
  change Ideal.Quotient.mk m (MvPowerSeries.C (e s)) = 0 ↔ s ∈ IsLocalRing.maximalIdeal S
  rw [Ideal.Quotient.eq_zero_iff_mem, PowerSeriesIs.Construction.PowerSeriesLocal.mem_maximalIdeal_iff,
    MvPowerSeries.constantCoeff_C]
  change s ∈ RingHom.ker e ↔ _
  rw [he]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.EtalePolynomial.Construction.EtalePolynomialFactorial
