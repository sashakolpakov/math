import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialHypersurface
import Mathlib.Data.Finset.Insert

/-! # Frame Correction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.FrameCorrection.Construction

noncomputable section

/-! Simultaneous square-zero lifting with finitely many prescribed coordinate values. -/

variable {k A B ι : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [DecidableEq ι]

/-- A finite family of dual coordinate derivations lets a square-zero
lift be corrected to preserve all prescribed coordinate values, while
retaining its original reduction modulo the square-zero ideal. -/
theorem exists_squareZero_coordinate_correction (f : A →ₐ[k] B)
    (D : ι → Derivation k A A) (z : ι → A) (t : ι → B)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0)
    (I : Ideal B) (hI : I ^ 2 = ⊥)
    (hft : ∀ i, Ideal.Quotient.mk I (f (z i)) = Ideal.Quotient.mk I (t i))
    (s : Finset ι) :
    ∃ g : A →ₐ[k] B, (∀ a : A, Ideal.Quotient.mk I (g a) = Ideal.Quotient.mk I (f a)) ∧
      ∀ i ∈ s, g (z i) = t i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨f, fun _ => rfl, fun _ h => False.elim (Finset.notMem_empty _ h)⟩
  | @insert i s hi ih =>
    obtain ⟨g, hg, hgs⟩ := ih
    let c := g (z i) - t i
    have hc : c ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change Ideal.Quotient.mk I (g (z i) - t i) = 0
      rw [map_sub, hg, hft, sub_self]
    have hsq : c * c = 0 := by
      have h := Ideal.mul_mem_mul hc hc
      rw [← pow_two, hI] at h
      exact h
    let g' := Smooth.DifferentialHypersurface.Construction.squareZeroDerivationCorrection g (D i) c hsq
    refine ⟨g', ?_, ?_⟩
    · intro a
      change Ideal.Quotient.mk I (g a - c * g (D i a)) = Ideal.Quotient.mk I (f a)
      rw [map_sub, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hc, zero_mul, sub_zero]
      exact hg a
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        change g (z i) - c * g (D i (z i)) = t i
        rw [hD, ite_eq_left rfl, map_one, mul_one]
        exact sub_sub_cancel (g (z i)) (t i)
      · have hij : i ≠ j := by intro h; exact hi (h.symm ▸ hj)
        change g (z j) - c * g (D i (z j)) = t j
        rw [hD, ite_eq_right hij, map_zero, mul_zero, sub_zero]
        exact hgs j hj

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.FrameCorrection.Construction
