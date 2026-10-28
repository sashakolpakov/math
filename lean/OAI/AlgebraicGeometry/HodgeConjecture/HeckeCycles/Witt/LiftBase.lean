import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-! # Lift Base -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.LiftBase.CM

noncomputable section

/-! A canonical complete DVR with the geometric residue field, and the
compatible map from the chosen q-adic integers. This supplies the base
needed to lift ordinary points of the actual smooth integral model. -/

variable (q : ℕ) [Fact q.Prime]

theorem padic_hom_value {F : Type*} [CommRing F] [CharP F q]
    (f : ℤ_[q] →+* F) (x : ℤ_[q]) : f x = (PadicInt.toZMod x : ZMod q).cast := by
  have hx := PadicInt.toZMod_spec x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hx
  obtain ⟨y, hy⟩ := hx
  have he : f x = f ((PadicInt.toZMod x : ZMod q).cast : ℤ_[q]) := by
    have hh := congrArg f hy
    simpa only [map_sub, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul,
      sub_eq_zero] using hh
  exact he.trans (by rw [ZMod.cast_eq_val, map_natCast, ZMod.cast_eq_val])

variable (k : Type) [Field k] [CharP k q] [PerfectRing k q]

theorem maximalIdeal_eq : IsLocalRing.maximalIdeal (WittVector q k) =
    Ideal.span {(q : WittVector q k)} := (WittVector.irreducible q).maximalIdeal_eq

theorem complete : IsAdicComplete (IsLocalRing.maximalIdeal (WittVector q k)) (WittVector q k) := by
  rw [CM.maximalIdeal_eq]
  infer_instance

def residueEquiv : IsLocalRing.ResidueField (WittVector q k) ≃+* k :=
  (Ideal.quotEquivOfEq (CM.maximalIdeal_eq q k)).trans WittVector.quotientPEquiv

theorem residueEquiv_residue (x : WittVector q k) :
    residueEquiv q k (IsLocalRing.residue (WittVector q k) x) = WittVector.constantCoeff x := rfl

def fromPadic : ℤ_[q] →+* WittVector q k :=
  (WittVector.map (ZMod.castHom (dvd_refl q) k)).comp (WittVector.fromPadicInt q)

theorem fromPadic_residue (x : ℤ_[q]) :
    residueEquiv q k (IsLocalRing.residue (WittVector q k) (fromPadic q k x)) =
      (PadicInt.toZMod x : ZMod q).cast :=
  (residueEquiv_residue q k (fromPadic q k x)).trans
    (padic_hom_value q (WittVector.constantCoeff.comp (fromPadic q k)) x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.LiftBase.CM
