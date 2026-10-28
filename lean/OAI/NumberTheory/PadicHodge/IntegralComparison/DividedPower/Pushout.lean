import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope
import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Relations

/-! # Pushout -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Pushout

noncomputable section

/-!
# IntegralComparison: the ring underlying a divided-power pushout

Start with the tensor product of the two rings. Form a relative
divided-power envelope for the left ring, then impose the divided-power
compatibility relations for the right ring. Both original rings map to
the resulting ring by actual divided-power morphisms.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
variable (I : Ideal B) (δ : DividedPowers I) (J : Ideal C) (ε : DividedPowers J)

abbrev Tensor := TensorProduct A B C

def leftRingMap : B →+* Tensor A B C := (Algebra.TensorProduct.includeLeft : B →ₐ[A] Tensor A B C).toRingHom

def rightRingMap : C →+* Tensor A B C := (Algebra.TensorProduct.includeRight : C →ₐ[A] Tensor A B C).toRingHom

def tensorIdeal : Ideal (Tensor A B C) := I.map (leftRingMap A B C) ⊔ J.map (rightRingMap A B C)

lemma left_ideal : I ≤ (tensorIdeal A B C I J).comap (leftRingMap A B C) :=
  fun _ hx => (show I.map (leftRingMap A B C) ≤ tensorIdeal A B C I J from le_sup_left)
    (Ideal.mem_map_of_mem _ hx)

abbrev Envelope := PowerEnvelope.Envelope B (Tensor A B C) I δ
  (leftRingMap A B C) (tensorIdeal A B C I J)

abbrev envelopeIdeal := PowerEnvelope.envelopeIdeal B (Tensor A B C) I δ
  (leftRingMap A B C) (tensorIdeal A B C I J)

abbrev envelopeDividedPowers := PowerEnvelope.envelopeDividedPowers B (Tensor A B C) I δ
  (leftRingMap A B C) (tensorIdeal A B C I J)

def toEnvelope : Tensor A B C →+* Envelope A B C I δ J :=
  PowerEnvelope.toEnvelope B (Tensor A B C) I δ
    (leftRingMap A B C) (tensorIdeal A B C I J)

def leftToEnvelope : DividedPowers.DPMorphism δ (envelopeDividedPowers A B C I δ J) where
  toRingHom := (toEnvelope A B C I δ J).comp (leftRingMap A B C)
  ideal_comp := (PowerEnvelope.envelopeTarget B (Tensor A B C) I δ
    (leftRingMap A B C) (tensorIdeal A B C I J) (left_ideal A B C I J)).baseCompatible.ideal_comp
  dpow_comp := (PowerEnvelope.envelopeTarget B (Tensor A B C) I δ
    (leftRingMap A B C) (tensorIdeal A B C I J) (left_ideal A B C I J)).baseCompatible.dpow_comp

def rightToEnvelope : C →+* Envelope A B C I δ J :=
  (toEnvelope A B C I δ J).comp (rightRingMap A B C)

lemma right_ideal {x : C} (hx : x ∈ J) : rightToEnvelope A B C I δ J x ∈ envelopeIdeal A B C I δ J :=
  PowerEnvelope.toEnvelope_mapsIdeal B (Tensor A B C) I δ
    (leftRingMap A B C) (tensorIdeal A B C I J)
      ((show J.map (rightRingMap A B C) ≤ tensorIdeal A B C I J from le_sup_right)
        (Ideal.mem_map_of_mem _ hx))

def relations : Set (Envelope A B C I δ J) :=
  {z | ∃ (n : ℕ) (_ : n ≠ 0) (x : C) (_ : x ∈ J), z =
    (envelopeDividedPowers A B C I δ J).dpow n (rightToEnvelope A B C I δ J x) -
      rightToEnvelope A B C I δ J (ε.dpow n x)}

lemma relations_subset : relations A B C I δ J ε ⊆ envelopeIdeal A B C I δ J := by
  rintro _ ⟨n, hn, x, hx, rfl⟩
  exact (envelopeIdeal A B C I δ J).sub_mem
    ((envelopeDividedPowers A B C I δ J).dpow_mem hn (right_ideal A B C I δ J hx))
    (right_ideal A B C I δ J (ε.dpow_mem hn hx))

abbrev Ring := Envelope A B C I δ J ⧸ Relations.relationIdeal
  (envelopeDividedPowers A B C I δ J) (relations A B C I δ J ε)

abbrev dividedPowers := Relations.dividedPowers
  (envelopeDividedPowers A B C I δ J) (relations A B C I δ J ε) (relations_subset A B C I δ J ε)

def quotientDP : DividedPowers.DPMorphism (envelopeDividedPowers A B C I δ J)
    (dividedPowers A B C I δ J ε) :=
  Relations.quotientMap (envelopeDividedPowers A B C I δ J)
    (relations A B C I δ J ε) (relations_subset A B C I δ J ε)

def leftMap : DividedPowers.DPMorphism δ (dividedPowers A B C I δ J ε) :=
  (quotientDP A B C I δ J ε).comp (leftToEnvelope A B C I δ J)

def rightMapRing : C →+* Ring A B C I δ J ε :=
  (quotientDP A B C I δ J ε).toRingHom.comp (rightToEnvelope A B C I δ J)

lemma rightMap_isDPMorphism : DividedPowers.IsDPMorphism ε (dividedPowers A B C I δ J ε)
    (rightMapRing A B C I δ J ε) := by
  apply (DividedPowers.isDPMorphism_iff _ _ _).mpr
  refine ⟨Ideal.map_le_iff_le_comap.mpr (fun x hx => ?_), ?_⟩
  · exact Ideal.mem_map_of_mem _ (right_ideal A B C I δ J hx)
  · intro n hn x hx
    change (dividedPowers A B C I δ J ε).dpow n
        ((quotientDP A B C I δ J ε) (rightToEnvelope A B C I δ J x)) =
      (quotientDP A B C I δ J ε) (rightToEnvelope A B C I δ J (ε.dpow n x))
    have hdp := (quotientDP A B C I δ J ε).dpow_comp (n := n)
      (rightToEnvelope A B C I δ J x) (right_ideal A B C I δ J hx)
    refine hdp.trans ?_
    apply sub_eq_zero.mp
    change (quotientDP A B C I δ J ε).toRingHom
        ((envelopeDividedPowers A B C I δ J).dpow n (rightToEnvelope A B C I δ J x)) -
      (quotientDP A B C I δ J ε).toRingHom (rightToEnvelope A B C I δ J (ε.dpow n x)) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Relations.relation_mem (envelopeDividedPowers A B C I δ J)
        (relations A B C I δ J ε) (relations_subset A B C I δ J ε) ⟨n, hn, x, hx, rfl⟩)

def rightMap : DividedPowers.DPMorphism ε (dividedPowers A B C I δ J ε) where
  toRingHom := rightMapRing A B C I δ J ε
  ideal_comp := (rightMap_isDPMorphism A B C I δ J ε).ideal_comp
  dpow_comp := (rightMap_isDPMorphism A B C I δ J ε).dpow_comp

lemma maps_agree : (leftMap A B C I δ J ε).toRingHom.comp (algebraMap A B) =
    (rightMap A B C I δ J ε).toRingHom.comp (algebraMap A C) := by
  apply RingHom.ext
  intro a
  change (quotientDP A B C I δ J ε) (toEnvelope A B C I δ J ((leftRingMap A B C) (algebraMap A B a))) =
    (quotientDP A B C I δ J ε) (toEnvelope A B C I δ J ((rightRingMap A B C) (algebraMap A C a)))
  congr 2
  exact ((Algebra.TensorProduct.includeLeft : B →ₐ[A] Tensor A B C).commutes a).trans
    ((Algebra.TensorProduct.includeRight : C →ₐ[A] Tensor A B C).commutes a).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Pushout
