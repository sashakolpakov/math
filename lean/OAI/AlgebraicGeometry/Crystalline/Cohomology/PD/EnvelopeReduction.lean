import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Envelope Reduction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeReduction.PDEnvelopeReduction

noncomputable section

/-!
# Cohomology: reduction of the relative divided-power envelope

The envelope maps canonically to the original quotient algebra. Its
divided-power ideal is the kernel of this map, so passage to the envelope
does not change the closed subscheme.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (I₀ : Ideal R) (δ₀ : DividedPowers I₀) (I : Ideal A)
variable (hbase : I₀.map (algebraMap R A) ≤ I)

/-- The original quotient as a target with zero divided-power ideal. -/
def quotientTarget : EnvelopeDp.PDEnvelope.Target R A I₀ δ₀ I where
  ring := CommRingCat.of (A ⧸ I)
  ideal := ⊥
  dp := dividedPowersBot (A ⧸ I)
  contains := by
    change I.map (Ideal.Quotient.mk I) ≤ ⊥
    rw [Ideal.map_quotient_self]
  baseDP :=
    { ideal_comp := by
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        change Ideal.Quotient.mk I (algebraMap R A r) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hbase (Ideal.mem_map_of_mem _ hr))
      dpow_comp := by
        intro n r hr
        have hx : Ideal.Quotient.mk I (algebraMap R A r) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (hbase (Ideal.mem_map_of_mem _ hr))
        change (dividedPowersBot (A ⧸ I)).dpow n
          (Ideal.Quotient.mk I (algebraMap R A r)) =
            Ideal.Quotient.mk I (algebraMap R A (δ₀.dpow n r))
        rw [hx]
        by_cases hn : n = 0
        · subst n
          rw [δ₀.dpow_zero hr, map_one, map_one, (dividedPowersBot (A ⧸ I)).dpow_zero (by simp)]
        · rw [(dividedPowersBot (A ⧸ I)).dpow_eval_zero hn]
          exact (Ideal.Quotient.eq_zero_iff_mem.mpr
            (hbase (Ideal.mem_map_of_mem _ (δ₀.dpow_mem hn hr)))).symm }

/-- The canonical reduction of the envelope to the original quotient. -/
def reduction : EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I →ₐ[A] A ⧸ I :=
  EnvelopeDp.PDEnvelope.lift R A I₀ δ₀ I (quotientTarget R A I₀ δ₀ I hbase)

@[simp]
theorem reduction_ofAlgebra (a : A) :
    reduction R A I₀ δ₀ I hbase (EnvelopeDp.PDEnvelope.ofAlgebra R A I₀ δ₀ I a) = Ideal.Quotient.mk I a := rfl

theorem reduction_surjective : Function.Surjective (reduction R A I₀ δ₀ I hbase) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨EnvelopeDp.PDEnvelope.ofAlgebra R A I₀ δ₀ I a, rfl⟩

theorem ideal_le_kernel : EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I ≤ RingHom.ker (reduction R A I₀ δ₀ I hbase).toRingHom := by
  intro x hx
  exact EnvelopeDp.PDEnvelope.evaluate_mem R A I₀ δ₀ I (quotientTarget R A I₀ δ₀ I hbase) hx

/-- The original quotient maps back to the quotient of the envelope by its ideal. -/
def quotientToQuotient : A ⧸ I →+* EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I ⧸ EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I)).comp (EnvelopeDp.PDEnvelope.ofAlgebra R A I₀ δ₀ I))
    (fun _a ha => Ideal.Quotient.eq_zero_iff_mem.mpr
      (EnvelopeDp.PDEnvelope.contains R A I₀ δ₀ I (Ideal.mem_map_of_mem _ ha)))

/-- Reduction descends through the envelope ideal. -/
def reductionQuotient : EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I ⧸ EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I →+* A ⧸ I :=
  Ideal.Quotient.lift (EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I) (reduction R A I₀ δ₀ I hbase).toRingHom
    (fun _ hx => ideal_le_kernel R A I₀ δ₀ I hbase hx)

theorem quotientToQuotient_reduction_term (t : EnvelopeDp.PDEnvelope.RingTerm A I) :
    quotientToQuotient R A I₀ δ₀ I (reduction R A I₀ δ₀ I hbase (EnvelopeDp.PDEnvelope.term R A I₀ δ₀ I t)) =
      Ideal.Quotient.mk (EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I) (EnvelopeDp.PDEnvelope.term R A I₀ δ₀ I t) := by
  cases t with
  | coeff a =>
    change quotientToQuotient R A I₀ δ₀ I (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I) (EnvelopeDp.PDEnvelope.ofAlgebra R A I₀ δ₀ I a)
    exact Ideal.Quotient.lift_mk _ _ _
  | add x y => rw [EnvelopeDp.PDEnvelope.term_add, map_add, map_add, map_add,
      quotientToQuotient_reduction_term x, quotientToQuotient_reduction_term y]
  | neg x => rw [EnvelopeDp.PDEnvelope.term_neg, map_neg, map_neg, map_neg, quotientToQuotient_reduction_term x]
  | mul x y => rw [EnvelopeDp.PDEnvelope.term_mul, map_mul, map_mul, map_mul,
      quotientToQuotient_reduction_term x, quotientToQuotient_reduction_term y]
  | ofIdeal x =>
    have hx : EnvelopeDp.PDEnvelope.idealTerm R A I₀ δ₀ I x ∈ EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I := Set.mem_range_self x
    change quotientToQuotient R A I₀ δ₀ I (reduction R A I₀ δ₀ I hbase (EnvelopeDp.PDEnvelope.idealTerm R A I₀ δ₀ I x)) =
      Ideal.Quotient.mk (EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I) (EnvelopeDp.PDEnvelope.idealTerm R A I₀ δ₀ I x)
    rw [show reduction R A I₀ δ₀ I hbase (EnvelopeDp.PDEnvelope.idealTerm R A I₀ δ₀ I x) = 0 from
        ideal_le_kernel R A I₀ δ₀ I hbase hx,
      map_zero, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
termination_by sizeOf t

theorem quotientToQuotient_reduction (x : EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I) :
    quotientToQuotient R A I₀ δ₀ I (reduction R A I₀ δ₀ I hbase x) =
      Ideal.Quotient.mk (EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I) x := by
  obtain ⟨t, rfl⟩ := Quotient.exists_rep x
  exact PDEnvelopeReduction.quotientToQuotient_reduction_term R A I₀ δ₀ I hbase t

theorem reductionQuotient_quotientToQuotient (x : A ⧸ I) :
    reductionQuotient R A I₀ δ₀ I hbase (quotientToQuotient R A I₀ δ₀ I x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [quotientToQuotient, reductionQuotient, Ideal.Quotient.lift_mk, RingHom.comp_apply]
  exact reduction_ofAlgebra R A I₀ δ₀ I hbase a

/-- Passing to the divided-power envelope preserves the original closed subscheme. -/
def quotientEquiv : EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I ⧸ EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I ≃+* A ⧸ I :=
  { reductionQuotient R A I₀ δ₀ I hbase with
    invFun := quotientToQuotient R A I₀ δ₀ I
    left_inv := by
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      change quotientToQuotient R A I₀ δ₀ I (reduction R A I₀ δ₀ I hbase a) =
        Ideal.Quotient.mk (EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I) a
      exact quotientToQuotient_reduction R A I₀ δ₀ I hbase a
    right_inv := reductionQuotient_quotientToQuotient R A I₀ δ₀ I hbase }

/-- The envelope ideal is exactly the kernel of its canonical reduction. -/
theorem reduction_kernel : RingHom.ker (reduction R A I₀ δ₀ I hbase).toRingHom = EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I := by
  apply le_antisymm _ (ideal_le_kernel R A I₀ δ₀ I hbase)
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [← quotientToQuotient_reduction R A I₀ δ₀ I hbase x,
    show reduction R A I₀ δ₀ I hbase x = 0 from hx, map_zero]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeReduction.PDEnvelopeReduction
