import OAI.AlgebraicGeometry.Divisors.LineBundles.MultiplicationSequence

/-! # Exact Sequence Length -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ExactSequenceLength.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite-length Euler characteristic of an exact sequence

The six-term identity follows by splitting the actual sequence at its
images and applying additivity of module length. Finiteness of the four
middle terms also gives finiteness at the ends. No alternating-length
identity is supplied as an assumption.
-/

variable {R A B C D E F : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

theorem moduleLengthNat_shortExact (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g)
    (hB : Module.length R B ≠ ⊤) :
    (Module.length R B).toNat = (Module.length R A).toNat + (Module.length R C).toNat := by
  have hA : Module.length R A ≠ ⊤ := ne_top_of_le_ne_top hB (Module.length_le_of_injective f hf)
  have hC : Module.length R C ≠ ⊤ := ne_top_of_le_ne_top hB (Module.length_le_of_surjective g hg)
  exact (congrArg ENat.toNat (Module.length_eq_add_of_exact f g hf hg h)).trans (ENat.toNat_add hA hC)

/-- Alternating length vanishes for the actual finite six-term exact sequence. -/
theorem moduleLengthNat_sixTerm (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : C →ₗ[R] D)
    (i : D →ₗ[R] E) (j : E →ₗ[R] F)
    (hf : Function.Injective f) (hj : Function.Surjective j)
    (hfg : Function.Exact f g) (hgh : Function.Exact g h)
    (hhi : Function.Exact h i) (hij : Function.Exact i j)
    (hB : Module.length R B ≠ ⊤) (hC : Module.length R C ≠ ⊤)
    (hD : Module.length R D ≠ ⊤) (hE : Module.length R E ≠ ⊤) :
    ((Module.length R A).toNat : ℤ) - (Module.length R B).toNat + (Module.length R C).toNat -
      (Module.length R D).toNat + (Module.length R E).toNat - (Module.length R F).toNat = 0 := by
  have h₁ := moduleLengthNat_shortExact f.range.subtype g.rangeRestrict
    f.range.subtype_injective g.surjective_rangeRestrict hfg.linearMap_rangeRestrict hB
  have h₂ := moduleLengthNat_shortExact g.range.subtype h.rangeRestrict
    g.range.subtype_injective h.surjective_rangeRestrict hgh.linearMap_rangeRestrict hC
  have h₃ := moduleLengthNat_shortExact h.range.subtype i.rangeRestrict
    h.range.subtype_injective i.surjective_rangeRestrict hhi.linearMap_rangeRestrict hD
  have h₄ := moduleLengthNat_shortExact i.range.subtype j.rangeRestrict
    i.range.subtype_injective j.surjective_rangeRestrict hij.linearMap_rangeRestrict hE
  have hleft : (Module.length R f.range).toNat = (Module.length R A).toNat :=
    congrArg ENat.toNat (LinearEquiv.ofInjective f hf).length_eq.symm
  have hright : (Module.length R j.range).toNat = (Module.length R F).toNat := by
    rw [LinearMap.range_eq_top.mpr hj, Module.length_top]
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ExactSequenceLength.BundleCycles
