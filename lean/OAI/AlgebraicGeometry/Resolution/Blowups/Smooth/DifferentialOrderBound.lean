import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.UnitCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.OrderBound
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativeOrder
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Differential Order Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialOrderBound.Construction

noncomputable section

/-! A finite intrinsic differential-order bound on arbitrary smooth integral affine algebras. -/

variable (k : Type*) {R : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]

/-- Every nonzero ideal of a smooth integral affine algebra has a finite
intrinsic differential-order bound. No global polynomial coordinates are assumed. -/
theorem exists_smooth_relative_differential_order_bound (J : Ideal R) (hJ : J ≠ ⊥) :
    ∃ n : ℕ, Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤ := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let F : ℕ →o Submodule R R :=
    ⟨Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J, Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order k J⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance F
  refine ⟨n, ?_⟩
  by_contra hproper
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) hproper
  let : q.IsMaximal := hq
  have hall (b : ℕ) : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J b ≤ q := by
    by_cases hb : b ≤ n
    · exact (Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order k J hb).trans hle
    · have he : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J b :=
        hn b (by omega)
      rwa [← he]
  obtain ⟨s, hs, d, pAlg, ht, he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := q)
  let A := Localization.Away s
  let : Algebra (MvPolynomial (Fin d) k) A := pAlg
  let : IsScalarTower k (MvPolynomial (Fin d) k) A := ht
  let : Algebra.IsStandardEtale (MvPolynomial (Fin d) k) A := he
  let : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway s
  have hs0 : s ≠ 0 := fun h => hs (h ▸ q.zero_mem)
  let : IsDomain A := Localization.Away.isDomain hs0
  have hJA : J.map (algebraMap R A) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hJ
  obtain ⟨b, hb⟩ := Blowups.Etale.OrderBound.Construction.exists_etale_differential_order_bound (σ := Fin d) (K := k)
    (J.map (algebraMap R A)) hJA
  have hrel : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map (algebraMap R A)) b = ⊤ :=
    (Blowups.Etale.RelativeOrder.Construction.etale_relative_differential_top_iff (σ := Fin d) (J.map (algebraMap R A)) b).mpr hb
  have hm := Ideal.map_mono (f := algebraMap R A) (hall b)
  rw [DifferentialNaturality.Construction.smooth_iteratedRelativeDifferentialIdeal_baseChange k J b, hrel] at hm
  have hne : q.map (algebraMap R A) ≠ ⊤ :=
    (IsLocalization.map_algebraMap_ne_top_iff_disjoint (Submonoid.powers s) A q).mpr
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hs)
  exact hne (top_le_iff.mp hm)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialOrderBound.Construction
