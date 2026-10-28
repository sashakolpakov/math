import OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFiniteness

/-! # Witt Unramified -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.WittUnramified

noncomputable section

/-! Unramifiedness of the finite Witt integer coefficient rings. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.WittFinite OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFiniteness IsLocalRing
variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Fintype k] [CharP k p]

theorem witt_maximalIdeal : maximalIdeal (WittVector p k) = Ideal.span {(p : WittVector p k)} :=
  (WittVector.irreducible p).maximalIdeal_eq

theorem witt_map_maximalIdeal :
    (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (WittVector p k)) = maximalIdeal (WittVector p k) := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast, witt_maximalIdeal]

instance wittLocalHom : IsLocalHom (algebraMap ℤ_[p] (WittVector p k)) :=
  ((local_hom_TFAE (algebraMap ℤ_[p] (WittVector p k))).out 3 1 rfl rfl).mp
    (le_of_eq (witt_map_maximalIdeal p k))

instance padicResidueFinite : Finite (ResidueField ℤ_[p]) :=
  Finite.of_injective (PadicInt.residueField (p := p)) (PadicInt.residueField (p := p)).injective

def wittResidueEquiv : ResidueField (WittVector p k) ≃+* k :=
  (Ideal.quotEquivOfEq (witt_maximalIdeal p k)).trans WittVector.quotientPEquiv

instance wittResidueFinite : Finite (ResidueField (WittVector p k)) :=
  Finite.of_injective (wittResidueEquiv p k) (wittResidueEquiv p k).injective

instance wittTorsionFree : Module.IsTorsionFree ℤ_[p] (WittVector p k) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (CoefficientFiniteness.padicToWitt_injective p k)

instance wittFree : Module.Free ℤ_[p] (WittVector p k) := inferInstance

instance wittFormallyUnramified : Algebra.FormallyUnramified ℤ_[p] (WittVector p k) :=
  Algebra.FormallyUnramified.of_map_maximalIdeal (witt_map_maximalIdeal p k)

instance wittEtale : Algebra.Etale ℤ_[p] (WittVector p k) := by
  let : Algebra.FinitePresentation ℤ_[p] (WittVector p k) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

theorem wittResidue_finrank :
    Module.finrank (ResidueField ℤ_[p]) (ResidueField (WittVector p k)) =
      (UnramifiedCoefficients.residueDegree (p := p) (k := k) : ℕ) := by
  apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
  have h := Module.natCard_eq_pow_finrank (K := ResidueField ℤ_[p])
    (V := ResidueField (WittVector p k))
  have hbase : Nat.card (ResidueField ℤ_[p]) = p := by
    rw [Nat.card_congr (PadicInt.residueField (p := p)).toEquiv, Nat.card_eq_fintype_card, ZMod.card]
  have htarget : Nat.card (ResidueField (WittVector p k)) = Fintype.card k := by
    rw [Nat.card_congr (wittResidueEquiv p k).toEquiv, Nat.card_eq_fintype_card]
  rw [hbase, htarget, UnramifiedCoefficients.residueDegree_card] at h
  exact h.symm

theorem witt_finrank : Module.finrank ℤ_[p] (WittVector p k) =
    (UnramifiedCoefficients.residueDegree (p := p) (k := k) : ℕ) := by
  rw [IsLocalRing.finrank_eq_finrank_residueField, wittResidue_finrank]

theorem coefficientField_finrank :
    Module.finrank ℚ_[p] (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) =
      (UnramifiedCoefficients.residueDegree (p := p) (k := k) : ℕ) := by
  rw [IsFractionRing.finrank_eq ℤ_[p] ℚ_[p] (WittVector p k)
    (UnramifiedCoefficients.CoefficientField (p := p) (k := k)), witt_finrank]

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.WittUnramified
