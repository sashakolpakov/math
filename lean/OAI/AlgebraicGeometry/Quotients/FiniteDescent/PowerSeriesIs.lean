import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Topology

/-! # Power Series Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesIs.Construction.PowerSeriesLocal

/-! Complete local structure on a power-series ring in finitely many variables. -/

open MvPowerSeries

variable {σ K : Type*} [Finite σ] [Field K]

omit [Finite σ] in
theorem mem_maximalIdeal_iff (f : MvPowerSeries σ K) :
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ↔ f.constantCoeff = 0 := by
  change ¬ IsUnit f ↔ _
  rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

theorem isAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries σ K)) (MvPowerSeries σ K) := by
  let I := MvPolynomial.idealOfVars σ K
  have hfg : I.FG := MvPolynomial.idealOfVars_fg σ K
  have hmax : I.IsMaximal := by
    have he : I = RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial σ K →+* K) := by
      ext f
      change f ∈ MvPolynomial.idealOfVars σ K ↔ MvPolynomial.constantCoeff f = 0
      rw [← pow_one (MvPolynomial.idealOfVars σ K), MvPolynomial.mem_pow_idealOfVars_iff']
      simp [Finsupp.degree_eq_zero_iff, MvPolynomial.constantCoeff_eq]
    rw [he]
    exact RingHom.ker_isMaximal_of_surjective _
      (fun a => ⟨MvPolynomial.C a, by simp⟩)
  have : I.IsMaximal := hmax
  let A := AdicCompletion I (MvPolynomial σ K)
  let J : Ideal A := I.map (algebraMap (MvPolynomial σ K) A)
  have hJ : J.IsMaximal := AdicCompletion.isMaximal_map_of_le I I le_rfl hfg
  have hcomp : IsAdicComplete J A := AdicCompletion.isAdicComplete_self I hfg
  let e : A ≃+* MvPowerSeries σ K := (toAdicCompletionAlgEquiv σ K).symm.toRingEquiv
  have hJe : (J.map e).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le e.surjective (by simp)
  have heq : J.map e = IsLocalRing.maximalIdeal (MvPowerSeries σ K) :=
    IsLocalRing.eq_maximalIdeal hJe
  rw [← heq]
  exact (IsAdicComplete.congr_ringEquiv J e).mpr hcomp

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesIs.Construction.PowerSeriesLocal
