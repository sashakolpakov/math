import OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing

/-! # Principal Kernel -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.PrincipalKernel

noncomputable section

/-!
# Lifting a principal kernel from reduction modulo p

The completion argument is isolated from the concrete tilt calculation.
Its hypotheses concern only a ring map, a regular image of p, and generation
of its kernel modulo p.
-/

section Hausdorff

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem submodule_isHausdorff (I : Ideal R) (N : Submodule R M) [IsHausdorff I M] :
    IsHausdorff I N := by
  constructor
  intro x hx
  apply Subtype.val_injective
  apply IsHausdorff.haus' (I := I)
  intro n
  rw [SModEq.sub_mem, sub_zero]
  have hn : x ∈ (I ^ n • ⊤ : Submodule R N) := by
    simpa only [SModEq.sub_mem, sub_zero] using hx n
  exact Submodule.smul_top_le_comap_smul_top (I ^ n) N.subtype hn

end Hausdorff

variable {R S : Type*} [CommRing R] [CommRing S]
variable (f : R →+* S) (ξ : R) (hξ : f ξ = 0)

def kernelMultiply : R →ₗ[R] RingHom.ker f where
  toFun a := ⟨ξ * a, by rw [RingHom.mem_ker, map_mul, hξ, zero_mul]⟩
  map_add' a b := Subtype.ext (mul_add ξ a b)
  map_smul' r a := by
    apply Subtype.ext
    change ξ * (r * a) = r * (ξ * a)
    ring

variable (p : ℕ) [IsPrecomplete (Ideal.span {(p : R)}) R]
  [IsHausdorff (Ideal.span {(p : R)}) R] [IsDomain S]

theorem kernelMultiply_surjective (hp : f (p : R) ≠ 0)
    (hmod : ∀ x : RingHom.ker f, ∃ b : R, (p : R) ∣ (x : R) - ξ * b) :
    Function.Surjective (kernelMultiply f ξ hξ) := by
  let _ : IsHausdorff (Ideal.span {(p : R)}) (RingHom.ker f) :=
    submodule_isHausdorff (Ideal.span {(p : R)}) (RingHom.ker f)
  apply surjective_of_mkQ_comp_surjective (I := Ideal.span {(p : R)})
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    ((Ideal.span {(p : R)}) • ⊤ : Submodule R (RingHom.ker f)) q
  obtain ⟨b, c, hc⟩ := hmod x
  have hc0 : f c = 0 := by
    have h := congrArg f hc
    rw [map_sub, map_mul, map_mul, RingHom.mem_ker.mp x.property, hξ,
      zero_mul, sub_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hp
  have he : x - kernelMultiply f ξ hξ b = (p : R) • (⟨c, hc0⟩ : RingHom.ker f) :=
    Subtype.ext hc
  have hm : x - kernelMultiply f ξ hξ b ∈
      ((Ideal.span {(p : R)}) • ⊤ : Submodule R (RingHom.ker f)) := by
    rw [he]
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) Submodule.mem_top
  refine ⟨b, ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  simpa only [neg_sub] using Submodule.neg_mem
    ((Ideal.span {(p : R)}) • ⊤ : Submodule R (RingHom.ker f)) hm

include hξ

/-- Generation of a p-saturated kernel modulo p lifts to a principal kernel. -/
theorem kernel_eq_span (hp : f (p : R) ≠ 0)
    (hmod : ∀ x : RingHom.ker f, ∃ b : R, (p : R) ∣ (x : R) - ξ * b) :
    RingHom.ker f = Ideal.span {ξ} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨b, hb⟩ := kernelMultiply_surjective f ξ hξ p hp hmod ⟨x, hx⟩
    rw [Ideal.mem_span_singleton]
    exact ⟨b, (congrArg Subtype.val hb).symm⟩
  · apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact hξ

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.PrincipalKernel
