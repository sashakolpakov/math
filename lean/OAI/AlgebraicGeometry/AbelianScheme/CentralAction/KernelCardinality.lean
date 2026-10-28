import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index

/-! # Kernel Cardinality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.KernelCardinality.Construction

noncomputable section

/-! A polarization relation controls the entire kernel of an isogeny.
The equal polarization-kernel factors cancel before any Tate comparison. -/

variable {G H I J : Type*} [Group G] [Group H] [Group I] [Group J]

/-- Fibers of a surjective group homomorphism all have the size of its kernel. -/
def kernelCompEquiv (f : G →* H) (hf : Function.Surjective f) (g : H →* I) :
    (g.comp f).ker ≃ f.ker × g.ker where
  toFun x :=
    (⟨x.val * (hf (f x.val)).choose⁻¹, by
      change f (x.val * (hf (f x.val)).choose⁻¹) = 1
      rw [map_mul, map_inv, (hf (f x.val)).choose_spec, mul_inv_cancel]⟩,
      ⟨f x.val, x.property⟩)
  invFun y := ⟨y.1.val * (hf y.2.val).choose, by
    change g (f (y.1.val * (hf y.2.val).choose)) = 1
    rw [map_mul, y.1.property, one_mul, (hf y.2.val).choose_spec]
    exact y.2.property⟩
  left_inv x := by
    apply Subtype.ext
    exact inv_mul_cancel_right _ _
  right_inv y := by
    have hy : f (y.1.val * (hf y.2.val).choose) = y.2.val := by
      rw [map_mul, y.1.property, one_mul, (hf y.2.val).choose_spec]
    apply Prod.ext
    · apply Subtype.ext
      change (y.1.val * (hf y.2.val).choose) *
        (hf (f (y.1.val * (hf y.2.val).choose))).choose⁻¹ = y.1.val
      rw [hy, mul_inv_cancel_right]
    · exact Subtype.ext hy

theorem kernel_comp_card (f : G →* H) (hf : Function.Surjective f) (g : H →* I) :
    Nat.card (g.comp f).ker = Nat.card f.ker * Nat.card g.ker :=
  (Nat.card_congr (kernelCompEquiv f hf g)).trans (Nat.card_prod _ _)

/-- If two finite polarization kernels have the same size, a polarization
relation with a p-primary multiplier forces the entire isogeny kernel to
be p-primary. No degree formula for the dual isogeny is needed. -/
theorem kernel_isPGroup_of_polarization
    (q : ℕ) (f : G →* H) (p : H →* I) (d : I →* J)
    (a : G →* J) (m : J →* J)
    (hf : Function.Surjective f) (ha : Function.Surjective a)
    [Finite a.ker] [Finite m.ker]
    (hcard : Nat.card a.ker = Nat.card p.ker)
    (hpol : d.comp (p.comp f) = m.comp a)
    (hm : IsPGroup q m.ker) : IsPGroup q f.ker := by
  have hle : (p.comp f).ker ≤ (m.comp a).ker := by
    intro x hx
    change (m.comp a) x = 1
    rw [← hpol, MonoidHom.comp_apply, hx, map_one]
  have hd := Subgroup.card_dvd_of_le hle
  rw [kernel_comp_card f hf p, kernel_comp_card a ha m, ← hcard,
    Nat.mul_comm (Nat.card f.ker)] at hd
  have hcancel : Nat.card f.ker ∣ Nat.card m.ker :=
    (Nat.mul_dvd_mul_iff_left (Nat.card_pos (α := a.ker))).mp hd
  obtain ⟨n, hn⟩ := hm.exists_card_dvd_pow
  exact IsPGroup.of_card_dvd_pow (hcancel.trans hn)

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.KernelCardinality.Construction
