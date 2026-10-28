import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.FiniteField
import OAI.Algorithms.SubexponentialSAT.LiftRing
import OAI.Algorithms.SubexponentialSAT.TableInterpolation
import OAI.Algorithms.SubexponentialSAT.LayoutSpec

namespace OAI.Algorithms

/-!
# The actual prime-power counting ring

The defining polynomial is the minimum polynomial already constructed for
`FiniteField.E p h`. A monic lift gives Lambda. Reduction followed by the
proved quotient equivalence lands in that exact field, not merely some field
of the same cardinality. The only numerical side conditions are positivity
of the modulus exponent and, for degree-dependent decoding, `h ≠ 0`.
-/

noncomputable section
namespace SubexponentialSAT.ActualLiftRing

open Polynomial

variable (p h μ : ℕ) [Fact p.Prime]

/-- Choose a monic lift when the modulus exponent is positive. The zero case
only keeps the type of the ring free of proof arguments and is never used by
counting. -/
def chosenF : (LiftRing.Base p μ)[X] :=
  if hμ : 0 < μ then
    (LiftRing.exists_monic_lift p μ hμ (FiniteField.definingPolynomial p h)
      (FiniteField.definingPolynomial_monic p h)).choose
  else 0

theorem chosenF_spec (hμ : 0 < μ) :
    (chosenF p h μ).map (LiftRing.baseReduction p μ hμ) =
        FiniteField.definingPolynomial p h ∧
      (chosenF p h μ).natDegree = (FiniteField.definingPolynomial p h).natDegree ∧
      (chosenF p h μ).Monic := by
  rw [chosenF, dite_eq_left hμ]
  exact (LiftRing.exists_monic_lift p μ hμ (FiniteField.definingPolynomial p h)
    (FiniteField.definingPolynomial_monic p h)).choose_spec

theorem F_map (hμ : 0 < μ) :
    (chosenF p h μ).map (LiftRing.baseReduction p μ hμ) =
      FiniteField.definingPolynomial p h := (chosenF_spec p h μ hμ).1

theorem F_monic (hμ : 0 < μ) : (chosenF p h μ).Monic :=
  (chosenF_spec p h μ hμ).2.2

theorem F_degree (hμ : 0 < μ) (hh : h ≠ 0) : (chosenF p h μ).natDegree = h :=
  (chosenF_spec p h μ hμ).2.1.trans (FiniteField.definingPolynomial_natDegree p h hh)

/-- Lambda = (Z/p^mu Z)[Y]/(chosen monic lift). -/
abbrev Ring := LiftRing.Lambda p μ (chosenF p h μ)

/-- Transport the reduced polynomial quotient to the exact interpolation field. -/
def reducedEquiv (hμ : 0 < μ) :
    LiftRing.Extension ((chosenF p h μ).map (LiftRing.baseReduction p μ hμ)) ≃+*
      FiniteField.E p h :=
  (Ideal.quotEquivOfEq
    (congrArg (fun f : (ZMod p)[X] => Ideal.span ({f} : Set (ZMod p)[X]))
      (F_map p h μ hμ))).trans
    (FiniteField.polynomialQuotientEquiv p h).toRingEquiv

/-- The actual residue map used in symbolic counting. -/
def rho (hμ : 0 < μ) : Ring p h μ →+* FiniteField.E p h :=
  (reducedEquiv p h μ hμ).toRingHom.comp
    (LiftRing.residue p μ hμ (chosenF p h μ))

theorem rho_surjective (hμ : 0 < μ) : Function.Surjective (rho p h μ hμ) :=
  (reducedEquiv p h μ hμ).surjective.comp
    (LiftRing.residue_surjective p μ hμ (chosenF p h μ))

theorem rho_eq_zero_iff (hμ : 0 < μ) (x : Ring p h μ) :
    rho p h μ hμ x = 0 ↔ (p : Ring p h μ) ∣ x := by
  change reducedEquiv p h μ hμ (LiftRing.residue p μ hμ (chosenF p h μ) x) = 0 ↔ _
  rw [← (reducedEquiv p h μ hμ).map_zero, (reducedEquiv p h μ hμ).injective.eq_iff]
  exact LiftRing.residue_eq_zero_iff p μ hμ (F_monic p h μ hμ) x

theorem rho_ker (hμ : 0 < μ) :
    RingHom.ker (rho p h μ hμ) = Ideal.span ({(p : Ring p h μ)} : Set (Ring p h μ)) := by
  ext x
  simp only [RingHom.mem_ker, Ideal.mem_span_singleton, rho_eq_zero_iff p h μ hμ]

theorem prime_power_zero : (p : Ring p h μ) ^ μ = 0 :=
  LiftRing.prime_power_zero p μ (chosenF p h μ)

/-- Lift prime-field coordinates using their standard integer representatives. -/
def coordinateLift (z : ZMod p) : Ring p h μ := (z.val : Ring p h μ)

theorem rho_coordinateLift (hμ : 0 < μ) (z : ZMod p) :
    rho p h μ hμ (coordinateLift p h μ z) = algebraMap (ZMod p) (FiniteField.E p h) z := by
  change rho p h μ hμ (z.val : Ring p h μ) = _
  rw [map_natCast]
  simpa only [map_natCast] using
    congrArg (algebraMap (ZMod p) (FiniteField.E p h)) (ZMod.natCast_zmod_val z)

theorem coordinateLift_unitDifferences :
    TableInterpolation.UnitDifferences (coordinateLift p h μ) := by
  intro a b hab
  apply TableInterpolation.unitDifferences_lambda_integerLabels p μ
    (Fact.out : p.Prime) (chosenF p h μ)
      (⟨a.val, a.val_lt⟩ : Fin p) (⟨b.val, b.val_lt⟩ : Fin p)
  intro heq
  apply hab
  have hv := congrArg Fin.val heq
  simpa using congrArg (fun n : ℕ => (n : ZMod p)) hv

/-- A residue section; no ring-homomorphism property is required or claimed. -/
def residueSection (hμ : 0 < μ) : CosetInvariance.ResidueSection (rho p h μ hμ) where
  lift z := (rho_surjective p h μ hμ z).choose
  residue_lift z := (rho_surjective p h μ hμ z).choose_spec

/-- Recover the integer represented by a constant element, using remainder
coordinates in the actual chosen polynomial quotient. -/
def decodeCount (hμ : 0 < μ) (x : Ring p h μ) : ℕ :=
  LiftRing.decodeCount p μ (F_monic p h μ hμ) x

theorem decodeCount_natCast (hμ : 0 < μ) (hh : h ≠ 0) (n : ℕ) (hn : n < p ^ μ) :
    decodeCount p h μ hμ (n : Ring p h μ) = n := by
  apply LiftRing.decodeCount_natCast p μ (F_monic p h μ hμ)
  · rw [F_degree p h μ hμ hh]
    exact Nat.pos_of_ne_zero hh
  · exact hn

theorem count_eq_zero_iff (hμ : 0 < μ) (hh : h ≠ 0) (n : ℕ) (hn : n < p ^ μ) :
    (n : Ring p h μ) = 0 ↔ n = 0 := by
  apply LiftRing.count_eq_zero_iff p μ (F_monic p h μ hμ)
  · rw [F_degree p h μ hμ hh]
    exact Nat.pos_of_ne_zero hh
  · exact hn

theorem natCast_injective_below (hμ : 0 < μ) (hh : h ≠ 0)
    {a b : ℕ} (ha : a < p ^ μ) (hb : b < p ^ μ)
    (hab : (a : Ring p h μ) = (b : Ring p h μ)) : a = b := by
  calc
    a = decodeCount p h μ hμ (a : Ring p h μ) := (decodeCount_natCast p h μ hμ hh a ha).symm
    _ = decodeCount p h μ hμ (b : Ring p h μ) := congrArg (decodeCount p h μ hμ) hab
    _ = b := decodeCount_natCast p h μ hμ hh b hb

section Layout

variable {p k Δ : ℕ} [Fact p.Prime]
  {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F]
  {P : Factor.Pattern V F} {c : LayoutSpec.Constants p k Δ}

/-- All rows and nodes of an actual layout lift to the chosen counting ring. -/
def liftedLayout (L : LayoutSpec.Layout (E := FiniteField.E p c.h) P c)
    (μ : ℕ) (hμ : 0 < μ) : LayoutSpec.LiftedLayout L (Ring p c.h μ) :=
  LayoutSpec.LiftedLayout.ofSurjective L (rho p c.h μ hμ) (rho_surjective p c.h μ hμ)

@[simp] theorem liftedLayout_residue
    (L : LayoutSpec.Layout (E := FiniteField.E p c.h) P c) (μ : ℕ) (hμ : 0 < μ) :
    (liftedLayout L μ hμ).residue = rho p c.h μ hμ := rfl

end Layout

end SubexponentialSAT.ActualLiftRing

end

end OAI.Algorithms
