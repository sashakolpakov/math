import Mathlib

/-! # Cayley Composition Phase -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCompositionPhase.Construction

noncomputable section

section

/-! The Cayley quadratic phase has the exact translation identity needed
to intertwine the two Weyl actions. -/

variable {F V : Type} [Field F] [CharZero F] [AddCommGroup V] [Module F V]
variable (β : LinearMap.BilinForm F V) (hAlt : ∀ x, β x x = 0)
variable (g D : V ≃ₗ[F] V)
variable (hg : ∀ x y, β (g x) (g y) = β x y) (hD : ∀ x, D x = g x - x)

def cayleyWeylPhase (v : V) : F := β (D.symm v) v / 2

include hAlt in
omit [CharZero F] in
theorem alternating_pairing_swap (x y : V) : β x y = -β y x := by
  have hh := hAlt (x + y)
  simp only [map_add, LinearMap.add_apply, hAlt] at hh
  exact eq_neg_of_add_eq_zero_left (by simpa only [zero_add, add_zero, add_comm] using hh)

include hD in
omit [CharZero F] in
theorem cayleyDifference_commutes (x : V) : D (g x) = g (D x) := by
  rw [hD, hD, map_sub]

include hAlt hg hD in
theorem cayleyWeylPhase_translation (u w : V) :
    cayleyWeylPhase β D (u - w) + β u w / 2 =
      cayleyWeylPhase β D (u - g w) + β (g w) u / 2 := by
  obtain ⟨x, rfl⟩ := D.surjective u
  obtain ⟨y, rfl⟩ := D.surjective w
  have hcomm := cayleyDifference_commutes g D hD y
  have hq1 : cayleyWeylPhase β D (D x - D y) = β (x - y) (D (x - y)) / 2 := by
    have hsub : D (x - y) = D x - D y := map_sub D x y
    rw [← hsub, cayleyWeylPhase, D.symm_apply_apply]
  have hq2 : cayleyWeylPhase β D (D x - g (D y)) =
      β (x - g y) (D (x - g y)) / 2 := by
    have hsub : D (x - g y) = D x - D (g y) := map_sub D x (g y)
    rw [← hcomm, ← hsub, cayleyWeylPhase, D.symm_apply_apply]
  rw [hq1, hq2]
  simp only [hD, map_sub, LinearMap.sub_apply, hg, hAlt,
    alternating_pairing_swap β hAlt x y,
    alternating_pairing_swap β hAlt x (g y),
    alternating_pairing_swap β hAlt (g x) y,
    alternating_pairing_swap β hAlt x (g (g y))]
  ring

include hAlt hg hD in
omit [CharZero F] in
theorem cayleyInverse_pairing (x y : V) :
    β (D.symm y) x = β (D.symm x) y + β x y := by
  obtain ⟨a, rfl⟩ := D.surjective x
  obtain ⟨b, rfl⟩ := D.surjective y
  rw [D.symm_apply_apply, D.symm_apply_apply]
  simp only [hD, map_sub, LinearMap.sub_apply, hg,
    alternating_pairing_swap β hAlt b (g a), alternating_pairing_swap β hAlt b a]
  ring

include hAlt hg hD in
theorem cayleyWeylPhase_output_shift (x v : V) :
    cayleyWeylPhase β D (x + v) + β (-v) (x + v) / 2 =
      cayleyWeylPhase β D x + cayleyWeylPhase β D v + β (D.symm v) x := by
  have hp := cayleyInverse_pairing β hAlt g D hg hD x v
  simp only [cayleyWeylPhase, map_add, LinearMap.add_apply,
    map_neg, LinearMap.neg_apply, hAlt]
  have hs := alternating_pairing_swap β hAlt v x
  linear_combination -(hp + hs) / 2

end

section

/-! Completing the square in the twisted convolution of two Cayley phases. -/

variable {F V : Type} [Field F] [CharZero F] [AddCommGroup V] [Module F V]
variable (β : LinearMap.BilinForm F V) (hAlt : ∀ x, β x x = 0)

omit [CharZero F] in
theorem cayleyWeylPhase_neg (D : V ≃ₗ[F] V) (x : V) :
    cayleyWeylPhase β D (-x) = cayleyWeylPhase β D x := by
  simp only [cayleyWeylPhase, map_neg, LinearMap.neg_apply, neg_neg]

include hAlt in
theorem cayleyWeylPhase_add (g D : V ≃ₗ[F] V)
    (hg : ∀ x y, β (g x) (g y) = β x y) (hD : ∀ x, D x = g x - x)
    (x v : V) :
    cayleyWeylPhase β D (x + v) = cayleyWeylPhase β D x +
      cayleyWeylPhase β D v + β (D.symm v) x + β v x / 2 := by
  have hh := cayleyWeylPhase_output_shift β hAlt g D hg hD x v
  simp only [map_add, map_neg, LinearMap.neg_apply, hAlt] at hh
  linear_combination hh

variable (g h Dg Dh Dgh : V ≃ₗ[F] V)
variable (hg : ∀ x y, β (g x) (g y) = β x y)
variable (hh : ∀ x y, β (h x) (h y) = β x y)
variable (hDg : ∀ x, Dg x = g x - x) (hDh : ∀ x, Dh x = h x - x)
variable (hDgh : ∀ x, Dgh x = g (h x) - x)

include hAlt hDg hDh hDgh in
theorem cayleyWeylPhase_composition_center (y : V) :
    cayleyWeylPhase β Dg (Dg (h y)) + cayleyWeylPhase β Dh (Dh y) +
      β (Dg (h y)) (Dh y) / 2 = cayleyWeylPhase β Dgh (Dgh y) := by
  simp only [cayleyWeylPhase, LinearEquiv.symm_apply_apply]
  simp only [hDg, hDh, hDgh, map_sub, LinearMap.sub_apply, hAlt]
  rw [alternating_pairing_swap β hAlt (g (h y)) (h y),
    alternating_pairing_swap β hAlt (g (h y)) y,
    alternating_pairing_swap β hAlt (h y) y]
  ring

include hAlt hg hh hDg hDh hDgh in
theorem cayleyWeylPhase_composition_shift (y t : V) :
    cayleyWeylPhase β Dg (t + Dg (h y)) + cayleyWeylPhase β Dh (-t + Dh y) +
      β (t + Dg (h y)) (-t + Dh y) / 2 =
      cayleyWeylPhase β Dgh (Dgh y) + cayleyWeylPhase β Dg t + cayleyWeylPhase β Dh t := by
  rw [cayleyWeylPhase_add β hAlt g Dg hg hDg,
    cayleyWeylPhase_add β hAlt h Dh hh hDh,
    Dg.symm_apply_apply, Dh.symm_apply_apply, cayleyWeylPhase_neg]
  have hcenter := cayleyWeylPhase_composition_center β hAlt g h Dg Dh Dgh hDg hDh hDgh y
  simp only [map_add, LinearMap.add_apply, map_neg, hAlt]
  have hcross : β t (Dh y) = -β (h y) t + β y t := by
    rw [hDh, map_sub, alternating_pairing_swap β hAlt t (h y),
      alternating_pairing_swap β hAlt t y]
    ring
  have hcross' : β (Dh y) t = β (h y) t - β y t := by
    rw [hDh, map_sub, LinearMap.sub_apply]
  rw [hcross, hcross']
  linear_combination hcenter

include hAlt hg hh hDg hDh hDgh in
theorem cayleyWeylPhase_composition_square (u v : V) :
    cayleyWeylPhase β Dg v + cayleyWeylPhase β Dh (u - v) + β v (u - v) / 2 =
      cayleyWeylPhase β Dgh u +
        cayleyWeylPhase β Dg (v - Dg (h (Dgh.symm u))) +
        cayleyWeylPhase β Dh (v - Dg (h (Dgh.symm u))) := by
  let y := Dgh.symm u
  have hsum : Dg (h y) + Dh y = u := by
    rw [hDg, hDh]
    have he := hDgh y
    rw [show Dgh y = u from Dgh.apply_symm_apply u] at he
    rw [he]
    abel
  have hright : -(v - Dg (h y)) + Dh y = u - v := by
    rw [← hsum]
    abel
  have heq := cayleyWeylPhase_composition_shift β hAlt g h Dg Dh Dgh hg hh hDg hDh hDgh
    y (v - Dg (h y))
  rw [sub_add_cancel, hright, show Dgh y = u from Dgh.apply_symm_apply u] at heq
  exact heq

end

section

/-! The Gaussian appearing in Cayley composition has a nondegenerate
symmetric polar form whenever all three Cayley differences are invertible. -/

variable {F V : Type} [Field F] [CharZero F] [AddCommGroup V] [Module F V]

def cayleySumLinearEquiv (Dg Dh Dgh : V ≃ₗ[F] V) : V ≃ₗ[F] V :=
  (Dh.symm.trans Dgh).trans Dg.symm

omit [CharZero F] in
theorem cayleySumLinearEquiv_apply (g h Dg Dh Dgh : V ≃ₗ[F] V)
    (hDg : ∀ x, Dg x = g x - x) (hDh : ∀ x, Dh x = h x - x)
    (hDgh : ∀ x, Dgh x = g (h x) - x) (v : V) :
    cayleySumLinearEquiv Dg Dh Dgh v = Dg.symm v + Dh.symm v + v := by
  obtain ⟨x, rfl⟩ := Dh.surjective v
  change Dg.symm (Dgh (Dh.symm (Dh x))) = _
  rw [Dh.symm_apply_apply]
  have hsum : Dgh x = Dg (h x) + Dh x := by
    rw [hDgh, hDg, hDh]
    abel
  rw [hsum, map_add, Dg.symm_apply_apply]
  rw [hDh]
  abel

def cayleySumForm (β : LinearMap.BilinForm F V) (Dg Dh : V ≃ₗ[F] V) :
    LinearMap.BilinForm F V :=
  LinearMap.comp β (Dg.symm.toLinearMap + Dh.symm.toLinearMap + LinearMap.id)

omit [CharZero F] in
theorem cayleySumForm_apply (β : LinearMap.BilinForm F V) (Dg Dh : V ≃ₗ[F] V) (x y : V) :
    cayleySumForm β Dg Dh x y = β (Dg.symm x + Dh.symm x + x) y := rfl

variable (β : LinearMap.BilinForm F V) (hAlt : ∀ x, β x x = 0)
variable (g h Dg Dh : V ≃ₗ[F] V)
variable (hg : ∀ x y, β (g x) (g y) = β x y)
variable (hh : ∀ x y, β (h x) (h y) = β x y)
variable (hDg : ∀ x, Dg x = g x - x) (hDh : ∀ x, Dh x = h x - x)

include hAlt hg hh hDg hDh in
omit [CharZero F] in
theorem cayleySumForm_symmetric (x y : V) :
    cayleySumForm β Dg Dh x y = cayleySumForm β Dg Dh y x := by
  have hp := cayleyInverse_pairing β hAlt g Dg hg hDg x y
  have hq := cayleyInverse_pairing β hAlt h Dh hh hDh x y
  simp only [cayleySumForm_apply, map_add, LinearMap.add_apply]
  rw [hp, hq, alternating_pairing_swap β hAlt y x]
  ring

include hDg hDh in
omit [CharZero F] in
theorem cayleySumForm_nondegenerate (hβ : β.Nondegenerate) (Dgh : V ≃ₗ[F] V)
    (hDgh : ∀ x, Dgh x = g (h x) - x) : (cayleySumForm β Dg Dh).Nondegenerate := by
  have heq (x y : V) : cayleySumForm β Dg Dh x y = β (cayleySumLinearEquiv Dg Dh Dgh x) y := by
    rw [cayleySumLinearEquiv_apply g h Dg Dh Dgh hDg hDh hDgh]
    rfl
  constructor
  · intro x hx
    apply (cayleySumLinearEquiv Dg Dh Dgh).injective
    rw [map_zero]
    apply hβ.1
    intro y
    rw [← heq]
    exact hx y
  · intro y hy
    apply hβ.2 y
    intro x
    obtain ⟨z, rfl⟩ := (cayleySumLinearEquiv Dg Dh Dgh).surjective x
    rw [← heq]
    exact hy z

include hAlt hg hh hDg hDh in
theorem cayleySumForm_polar (x y : V) :
    cayleyWeylPhase β Dg (x + y) + cayleyWeylPhase β Dh (x + y) =
      (cayleyWeylPhase β Dg x + cayleyWeylPhase β Dh x) +
      (cayleyWeylPhase β Dg y + cayleyWeylPhase β Dh y) + cayleySumForm β Dg Dh x y := by
  rw [cayleyWeylPhase_add β hAlt g Dg hg hDg,
    cayleyWeylPhase_add β hAlt h Dh hh hDh]
  rw [cayleySumForm_symmetric β hAlt g h Dg Dh hg hh hDg hDh x y]
  simp only [cayleySumForm_apply, map_add, LinearMap.add_apply]
  ring

end

/-! The Fourier frequency and residual phase that identify the scalar in
the composition of actual Cayley operators. -/

variable {F V : Type} [Field F] [CharZero F] [AddCommGroup V] [Module F V]

def cayleyCompositionShift (h Dg Dgh : V ≃ₗ[F] V) : V ≃ₗ[F] V :=
  (Dgh.symm.trans h).trans Dg

variable (g h Dg Dh Dgh : V ≃ₗ[F] V)
variable (hDg : ∀ x, Dg x = g x - x) (hDh : ∀ x, Dh x = h x - x)
variable (hDgh : ∀ x, Dgh x = g (h x) - x)

include hDg hDh hDgh in
omit [CharZero F] in
theorem cayleyCompositionShift_sum (x : V) :
    Dg.symm (cayleyCompositionShift h Dg Dgh x) +
      Dh.symm (cayleyCompositionShift h Dg Dgh x) + cayleyCompositionShift h Dg Dgh x =
        Dh.symm x + x := by
  let y := Dgh.symm x
  have hsum : x = Dg (h y) + Dh y := by
    rw [hDg, hDh]
    have he := hDgh y
    rw [show Dgh y = x from Dgh.apply_symm_apply x] at he
    rw [he]
    abel
  change Dg.symm (Dg (h y)) + Dh.symm (Dg (h y)) + Dg (h y) = Dh.symm x + x
  rw [Dg.symm_apply_apply, hsum, map_add, Dh.symm_apply_apply, hDh]
  abel

variable (β : LinearMap.BilinForm F V) (hAlt : ∀ x, β x x = 0)
variable (hg : ∀ x y, β (g x) (g y) = β x y)
variable (hh : ∀ x y, β (h x) (h y) = β x y)

include hDg hDh hDgh hAlt hg hh in
omit [CharZero F] in
theorem cayleySumForm_composition_frequency (v x : V) :
    cayleySumForm β Dg Dh v (-cayleyCompositionShift h Dg Dgh x) = β (-(Dh.symm v)) x := by
  rw [cayleySumForm_symmetric β hAlt g h Dg Dh hg hh hDg hDh,
    map_neg, LinearMap.neg_apply, cayleySumForm_apply,
    cayleyCompositionShift_sum g h Dg Dh Dgh hDg hDh hDgh]
  have hp := cayleyInverse_pairing β hAlt h Dh hh hDh x v
  simp only [map_add, LinearMap.add_apply, map_neg, LinearMap.neg_apply]
  rw [hp]

include hDg hDh hDgh hAlt hg hh in
theorem cayleyComposition_residual_phase (x : V) :
    cayleyWeylPhase β Dh x -
      (cayleyWeylPhase β Dg (-cayleyCompositionShift h Dg Dgh x) +
        cayleyWeylPhase β Dh (-cayleyCompositionShift h Dg Dgh x)) =
      cayleyWeylPhase β Dgh x := by
  have he := cayleyWeylPhase_composition_square β hAlt g h Dg Dh Dgh hg hh hDg hDh hDgh x 0
  have hz : cayleyWeylPhase β Dg 0 = 0 := by simp only [cayleyWeylPhase, map_zero, zero_div]
  simp only [hz, sub_zero, zero_sub, map_zero, LinearMap.zero_apply, zero_div, zero_add, add_zero] at he
  change cayleyWeylPhase β Dh x -
    (cayleyWeylPhase β Dg (-Dg (h (Dgh.symm x))) +
      cayleyWeylPhase β Dh (-Dg (h (Dgh.symm x)))) = _
  linear_combination he

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCompositionPhase.Construction
