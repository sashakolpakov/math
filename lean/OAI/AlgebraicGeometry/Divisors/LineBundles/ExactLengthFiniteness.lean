import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.PeriodicComplex

/-! # Exact Length Finiteness -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ExactLengthFiniteness.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite length through the actual homology sequence

In an exact A → M → B, finite length of A and B implies finite
length of M. Applied to the actual periodic homology sequence, this
provides the missing finiteness term of a short exact sequence.
-/

open _root_.CategoryTheory _root_.HomologicalComplex

variable {R A M B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M]
    [AddCommGroup B] [Module R B]

theorem moduleLength_ne_top_of_exact (f : A →ₗ[R] M) (g : M →ₗ[R] B)
    (h : Function.Exact f g) (hA : Module.length R A ≠ ⊤) (hB : Module.length R B ≠ ⊤) :
    Module.length R M ≠ ⊤ := by
  have hf : Module.length R f.range ≠ ⊤ :=
    ne_top_of_le_ne_top hA (Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict)
  have hg : Module.length R g.range ≠ ⊤ :=
    ne_top_of_le_ne_top hB (Module.length_le_of_injective g.range.subtype g.range.subtype_injective)
  rw [Module.length_eq_add_of_exact f.range.subtype g.rangeRestrict
    f.range.subtype_injective g.surjective_rangeRestrict h.linearMap_rangeRestrict]
  exact (ENat.add_lt_top.mpr ⟨hf.lt_top, hg.lt_top⟩).ne

theorem periodicComplexShape_rel_not (i : Bool) : Periodic.PeriodicComplex.BundleCycles.periodicComplexShape.Rel i (!i) := by
  cases i
  · exact Periodic.PeriodicComplex.BundleCycles.periodicComplexShape_false_true
  · exact Periodic.PeriodicComplex.BundleCycles.periodicComplexShape_true_false

theorem periodicShortExact_homology_finite_right
    (S : ShortComplex (HomologicalComplex (ModuleCat R) Periodic.PeriodicComplex.BundleCycles.periodicComplexShape)) (hS : S.ShortExact)
    (hA : ∀ i : Bool, Module.length R (S.X₁.homology i) ≠ ⊤)
    (hB : ∀ i : Bool, Module.length R (S.X₂.homology i) ≠ ⊤) (i : Bool) :
    Module.length R (S.X₃.homology i) ≠ ⊤ :=
  moduleLength_ne_top_of_exact (homologyMap S.g i).hom
    (hS.δ i (!i) (periodicComplexShape_rel_not i)).hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ i (!i) (periodicComplexShape_rel_not i))) (hB i) (hA (!i))

theorem periodicShortExact_homology_finite_middle
    (S : ShortComplex (HomologicalComplex (ModuleCat R) Periodic.PeriodicComplex.BundleCycles.periodicComplexShape)) (hS : S.ShortExact)
    (hA : ∀ i : Bool, Module.length R (S.X₁.homology i) ≠ ⊤)
    (hC : ∀ i : Bool, Module.length R (S.X₃.homology i) ≠ ⊤) (i : Bool) :
    Module.length R (S.X₂.homology i) ≠ ⊤ :=
  moduleLength_ne_top_of_exact (homologyMap S.f i).hom (homologyMap S.g i).hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₂ i)) (hA i) (hC i)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ExactLengthFiniteness.BundleCycles
