import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KernelCardinalityCard
import Mathlib.GroupTheory.PGroup

/-! # Polarized Kernel Groups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedKernelGroups.KernelCardinality

noncomputable section

/-! A polarization diagram with equal finite polarization kernels forces
the isogeny kernel to be primary at the multiplier prime. Coprimality of
the polarization degree then gives the exact multiplier annihilator. -/

variable {A B A' B' : Type*} [CommGroup A] [CommGroup B]
  [CommGroup A'] [CommGroup B']

theorem polarized_card_kernel
    (f : A →* B) (p : A →* A') (r : B →* B') (d : B' →* A')
    (n : A →* A) (hf : Function.Surjective f) (hr : Function.Surjective r)
    (hn : Function.Surjective n) [Finite p.ker]
    (hcard : Nat.card p.ker = Nat.card r.ker)
    (hdiag : (d.comp r).comp f = p.comp n) :
    Nat.card f.ker * Nat.card d.ker = Nat.card n.ker := by
  have h₁ := KernelCardinalityCard.KernelCardinality.card_comp_kernel f (d.comp r) hf
  have h₂ := KernelCardinalityCard.KernelCardinality.card_comp_kernel r d hr
  have h₃ := KernelCardinalityCard.KernelCardinality.card_comp_kernel n p hn
  have h₄ := congrArg (fun z : A →* A' => Nat.card z.ker) hdiag
  have he : (Nat.card f.ker * Nat.card d.ker) * Nat.card p.ker =
      Nat.card n.ker * Nat.card p.ker := by
    calc
      _ = Nat.card f.ker * (Nat.card r.ker * Nat.card d.ker) := by rw [hcard]; ac_rfl
      _ = Nat.card ((d.comp r).comp f).ker := (h₁.trans (congrArg (Nat.card f.ker * ·) h₂)).symm
      _ = Nat.card (p.comp n).ker := h₄
      _ = _ := h₃
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos he

variable (f : A →* B) (p : A →* A') (r : B →* B') (d : B' →* A')
  (q m : ℕ) [Fact q.Prime]
  (hf : Function.Surjective f) (hr : Function.Surjective r)
  (hm : Function.Surjective (powMonoidHom (q ^ m) : A →* A))
  [Finite p.ker] [Finite (powMonoidHom (q ^ m) : A →* A).ker]
  (hcard : Nat.card p.ker = Nat.card r.ker)
  (hdiag : (d.comp r).comp f = p.comp (powMonoidHom (q ^ m)))

include hf hr hm hcard hdiag

theorem polarized_kernel_isPGroup : IsPGroup q f.ker := by
  have hp : IsPGroup q (powMonoidHom (q ^ m) : A →* A).ker := by
    intro x
    exact ⟨m, Subtype.ext x.property⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  apply IsPGroup.of_card_dvd_pow (n := n)
  refine ⟨Nat.card d.ker, ?_⟩
  exact hn.symm.trans (polarized_card_kernel f p r d (powMonoidHom (q ^ m)) hf hr hm hcard hdiag).symm

theorem polarized_kernel_killed
    (hq : q.Coprime (Nat.card p.ker)) (x : A) (hx : f x = 1) : x ^ (q ^ m) = 1 := by
  have hp : p (x ^ (q ^ m)) = 1 := by
    have he := DFunLike.congr_fun hdiag x
    simpa only [MonoidHom.comp_apply, powMonoidHom_apply, hx, map_one] using he.symm
  let y : p.ker := ⟨x ^ (q ^ m), hp⟩
  have hy : (x ^ (q ^ m)) ^ Nat.card p.ker = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := y))
  let z : f.ker := ⟨x, hx⟩
  have hG := polarized_kernel_isPGroup f p r d q m hf hr hm hcard hdiag
  have hz : (hG.powEquiv hq) (z ^ (q ^ m)) = (hG.powEquiv hq) 1 := by
    apply Subtype.ext
    simpa only [IsPGroup.powEquiv_apply, Subgroup.coe_pow, Subgroup.coe_one, one_pow] using hy
  exact congrArg Subtype.val ((hG.powEquiv hq).injective hz)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedKernelGroups.KernelCardinality
