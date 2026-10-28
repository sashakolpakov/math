import Mathlib.RingTheory.Etale.Kaehler
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialIdealTransform

/-! # Derivation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Derivation.Construction

noncomputable section

/-! Extension of derivations across étale coordinate changes. -/

open TensorProduct

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
variable [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
variable [Algebra.FormallyEtale R S]

/-- A derivation with values in the étale algebra extends to that algebra,
using the actual base-change isomorphism of Kähler differential modules. -/
def extendEtaleDerivation (D : Derivation k R S) : Derivation k S S :=
  ((LinearMap.liftBaseChange S D.liftKaehlerDifferential).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R S).symm.toLinearMap).compDer
      (KaehlerDifferential.D k S)

/-- The extension agrees with the original derivation on base elements. -/
theorem extendEtaleDerivation_algebraMap (D : Derivation k R S) (r : R) :
    extendEtaleDerivation D (algebraMap R S r) = D r := by
  change LinearMap.liftBaseChange S D.liftKaehlerDifferential
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R S).symm
      (KaehlerDifferential.D k S (algebraMap R S r))) = D r
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]

/-- In particular, a derivation of the base ring extends after mapping its
values into the étale algebra. -/
def extendEtaleRingDerivation (D : Derivation k R R) : Derivation k S S :=
  extendEtaleDerivation ((Algebra.linearMap R S).compDer D)

theorem extendEtaleRingDerivation_algebraMap (D : Derivation k R R) (r : R) :
    extendEtaleRingDerivation (S := S) D (algebraMap R S r) = algebraMap R S (D r) :=
  extendEtaleDerivation_algebraMap ((Algebra.linearMap R S).compDer D) r

/-- A derivation on an étale algebra is determined by its restriction to
the original algebra. -/
theorem etaleDerivation_ext (D E : Derivation k S S)
    (h : ∀ r : R, D (algebraMap R S r) = E (algebraMap R S r)) : D = E := by
  have hlin : D.liftKaehlerDifferential = E.liftKaehlerDifferential := by
    apply (KaehlerDifferential.isBaseChange_of_formallyEtale k R S).algHom_ext'
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro r
    change D.liftKaehlerDifferential
        (KaehlerDifferential.map k k R S (KaehlerDifferential.D k R r)) =
      E.liftKaehlerDifferential
        (KaehlerDifferential.map k k R S (KaehlerDifferential.D k R r))
    rw [KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact h r
  apply Derivation.ext
  intro s
  rw [← Derivation.liftKaehlerDifferential_comp_D D s,
    ← Derivation.liftKaehlerDifferential_comp_D E s, hlin]

theorem existsUnique_etaleDerivation_extension (D : Derivation k R S) :
    ∃! E : Derivation k S S, ∀ r : R, E (algebraMap R S r) = D r := by
  refine ⟨extendEtaleDerivation D, extendEtaleDerivation_algebraMap D, ?_⟩
  intro E hE
  apply etaleDerivation_ext (R := R)
  intro r
  rw [hE, extendEtaleDerivation_algebraMap]

omit [Algebra k R] [Algebra k S] [IsScalarTower k R S] in
/-- First differential ideals map into the corresponding differential ideals
after an étale coordinate change. -/
theorem firstDifferentialIdeal_map_le_of_etale (J : Ideal R) :
    (DifferentialIdealTransform.Construction.firstDifferentialIdeal J).map (algebraMap R S) ≤
      DifferentialIdealTransform.Construction.firstDifferentialIdeal (J.map (algebraMap R S)) := by
  rw [Ideal.map_le_iff_le_comap]
  apply sup_le
  · intro r hr
    exact DifferentialIdealTransform.Construction.le_firstDifferentialIdeal _ (Ideal.mem_map_of_mem _ hr)
  · apply Ideal.span_le.mpr
    rintro r ⟨⟨D, p⟩, rfl⟩
    change algebraMap R S (D p.val) ∈ DifferentialIdealTransform.Construction.firstDifferentialIdeal (J.map (algebraMap R S))
    rw [← extendEtaleRingDerivation_algebraMap (k := ℤ) (S := S) D p.val]
    exact DifferentialIdealTransform.Construction.derivation_mem_firstDifferentialIdeal _ (extendEtaleRingDerivation (S := S) D)
      (Ideal.mem_map_of_mem _ p.property)

omit [Algebra k R] [Algebra k S] [IsScalarTower k R S] in
/-- The differential equation used for persistence stays in the same-order
differential ideal after an étale coordinate change. -/
theorem iteratedDifferentialIdeal_map_le_of_etale (J : Ideal R) (n : ℕ) :
    (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n).map (algebraMap R S) ≤
      DifferentialIdealTransform.Construction.iteratedDifferentialIdeal (J.map (algebraMap R S)) n := by
  induction n generalizing J with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih (DifferentialIdealTransform.Construction.firstDifferentialIdeal J)).trans
      (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_mono n (firstDifferentialIdeal_map_le_of_etale J))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Derivation.Construction
