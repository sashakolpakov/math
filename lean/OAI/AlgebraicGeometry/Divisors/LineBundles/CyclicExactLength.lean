import OAI.AlgebraicGeometry.Divisors.LineBundles.ExactSequenceLength

/-! # Cyclic Exact Length -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.CyclicExactLength.BundleCycles

noncomputable section

/-!
# LineBundleCycles: length cancellation in a cyclic six-term sequence

Unlike a bounded six-term sequence, the last map here returns to the
first module. Splitting at all six images proves the alternating length
identity used by the homology sequence of a two-periodic complex.
-/

variable {R A B C D E F : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

theorem moduleLengthNat_cyclicSixTerm
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : C →ₗ[R] D)
    (i : D →ₗ[R] E) (j : E →ₗ[R] F) (k : F →ₗ[R] A)
    (hfg : Function.Exact f g) (hgh : Function.Exact g h)
    (hhi : Function.Exact h i) (hij : Function.Exact i j)
    (hjk : Function.Exact j k) (hkf : Function.Exact k f)
    (hA : Module.length R A ≠ ⊤) (hB : Module.length R B ≠ ⊤)
    (hC : Module.length R C ≠ ⊤) (hD : Module.length R D ≠ ⊤)
    (hE : Module.length R E ≠ ⊤) (hF : Module.length R F ≠ ⊤) :
    ((Module.length R A).toNat : ℤ) - (Module.length R B).toNat +
      (Module.length R C).toNat - (Module.length R D).toNat +
      (Module.length R E).toNat - (Module.length R F).toNat = 0 := by
  have h₁ := ExactSequenceLength.BundleCycles.moduleLengthNat_shortExact k.range.subtype f.rangeRestrict
    k.range.subtype_injective f.surjective_rangeRestrict hkf.linearMap_rangeRestrict hA
  have h₂ := ExactSequenceLength.BundleCycles.moduleLengthNat_shortExact f.range.subtype g.rangeRestrict
    f.range.subtype_injective g.surjective_rangeRestrict hfg.linearMap_rangeRestrict hB
  have h₃ := ExactSequenceLength.BundleCycles.moduleLengthNat_shortExact g.range.subtype h.rangeRestrict
    g.range.subtype_injective h.surjective_rangeRestrict hgh.linearMap_rangeRestrict hC
  have h₄ := ExactSequenceLength.BundleCycles.moduleLengthNat_shortExact h.range.subtype i.rangeRestrict
    h.range.subtype_injective i.surjective_rangeRestrict hhi.linearMap_rangeRestrict hD
  have h₅ := ExactSequenceLength.BundleCycles.moduleLengthNat_shortExact i.range.subtype j.rangeRestrict
    i.range.subtype_injective j.surjective_rangeRestrict hij.linearMap_rangeRestrict hE
  have h₆ := ExactSequenceLength.BundleCycles.moduleLengthNat_shortExact j.range.subtype k.rangeRestrict
    j.range.subtype_injective k.surjective_rangeRestrict hjk.linearMap_rangeRestrict hF
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.CyclicExactLength.BundleCycles
