import OAI.RepresentationTheory.Theta.Adelic.PrincipalLocalCoefficients
import OAI.RepresentationTheory.Theta.Adelic.PrincipalDenominator
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RestrictedIntegralNeighborhoods

/-! # Principal Finite Cofinal -/

namespace OAI.RepresentationTheory.Theta.Adelic.PrincipalFiniteCofinal

noncomputable section

/-! The literal rational coefficient principal levels are cofinal in
the actual finite special-unitary restricted-product topology. -/

open scoped Classical _root_.NumberField _root_.Topology

open OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RestrictedIntegralNeighborhoods.CM
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.IntegralTopology
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup OAI.RepresentationTheory.Theta.Adelic.PrincipalDenominator
open OAI.RepresentationTheory.Theta.Adelic.PrincipalLocalCoefficients

variable (F : Type) [Field F] [NumberField F] {d : F}
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

theorem principal_finite_cofinal (L : OpenSubgroup (FiniteSchwartz.FiniteSU F H)) :
    ∃ D : ℕ, 0 < D ∧ ∀ N : ℕ, D ∣ N →
      ∀ g : SpecialUnitary.SU H.val, BallGeometryData.PrincipalLevel N g → RationalSU.rationalFiniteSU F H g ∈ L := by
  obtain ⟨t, ht, q, hq⟩ := PrincipalDenominator.exists_positive_integral_multiple F d
  obtain ⟨J, V, hV, hsub⟩ := AlgebraicGeometry.HodgeConjecture.ThetaCycle.RestrictedIntegralNeighborhoods.CM.restricted_integral_neighborhood
    (G := fun v : FiniteSchwartz.FinitePlace F => SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)))
    (fun v => IntegralTopology.localSUIntegral F H.val (.inr v))
    (L : Set (FiniteSchwartz.FiniteSU F H)) (L.isOpen.mem_nhds L.one_mem)
  have hn (v : FiniteSchwartz.FinitePlace F) := AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalUnitaryNeighborhoods.CM.local_unitary_integer_neighborhood F v
    (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d) (SpecialUnitary.specialUnitary (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)))
    (V v) (hV v)
  choose n hn0 hlocal using hn
  let c : ℤ := ∏ v ∈ J, n v
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => hn0 v)
  refine ⟨t * c.natAbs, Nat.mul_pos ht (Int.natAbs_pos.mpr hc), ?_⟩
  intro N hN g hg
  have htN : t ∣ N := dvd_trans (dvd_mul_right t c.natAbs) hN
  obtain ⟨r, hr⟩ := PrincipalDenominator.integral_multiple_of_dvd F d t N q hq htN
  have hcN : c ∣ (N : ℤ) := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa only [Int.natAbs_natCast] using dvd_trans (dvd_mul_left c.natAbs t) hN
  apply hsub (RationalSU.rationalFiniteSU F H g)
  · intro v
    exact PrincipalLocalCoefficients.principal_local_integral F H N r hr g hg v
  · intro v hv
    have hvN : n v ∣ (N : ℤ) := dvd_trans (Finset.dvd_prod_of_mem n hv) hcN
    obtain ⟨a, ha, he⟩ := PrincipalLocalCoefficients.principal_local_tuple F H N g hg
      (PrincipalSubgroup.principalLevel_inv F d H N r hr g hg) v (n v) hvN
    exact hlocal v a ha (RationalSU.rationalLocalSU F H (.inr v) g) he

end

end OAI.RepresentationTheory.Theta.Adelic.PrincipalFiniteCofinal
