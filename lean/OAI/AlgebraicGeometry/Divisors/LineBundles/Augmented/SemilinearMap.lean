import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarGrading
import Mathlib.LinearAlgebra.Prod

/-! # Semilinear Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SemilinearMap.BundleCycles

noncomputable section

/-! Augmentation of actual semilinear module maps, including the
generation property needed for the projective symmetric construction. -/

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] (f : R →+* S) (g : M →ₛₗ[f] N)

def augmentedSemilinearMap : R × M →ₛₗ[f] S × N where
  toFun v := (f v.1, g v.2)
  map_add' v w := by ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add]
  map_smul' r v := by
    ext
    · exact map_mul f r v.1
    · exact g.map_smulₛₗ r v.2

theorem augmentedSemilinearMap_variable : augmentedSemilinearMap f g (1, 0) = (1, 0) := by
  change (f 1, g 0) = (1, 0)
  rw [map_one, map_zero]

theorem augmentedSemilinearMap_span (hgen : Submodule.span S (Set.range g) = ⊤) :
    Submodule.span S (Set.range (augmentedSemilinearMap f g)) = ⊤ := by
  let T := Submodule.span S (Set.range (augmentedSemilinearMap f g))
  have hfirst : ∀ s : S, (s, (0 : N)) ∈ T := by
    intro s
    have h : ((1 : S), (0 : N)) ∈ T :=
      Submodule.subset_span ⟨(1, 0), augmentedSemilinearMap_variable f g⟩
    simpa only [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero] using T.smul_mem s h
  have hsecond : ∀ n : N, ((0 : S), n) ∈ T := by
    intro n
    have hn : n ∈ Submodule.span S (Set.range g) := by rw [hgen]; trivial
    induction hn using Submodule.span_induction with
    | mem n hn =>
      obtain ⟨m, rfl⟩ := hn
      apply Submodule.subset_span
      refine ⟨(0, m), ?_⟩
      change (f 0, g m) = (0, g m)
      rw [map_zero]
    | zero => exact T.zero_mem
    | add x y hx hy ihx ihy =>
      simpa only [Prod.mk_add_mk, zero_add] using T.add_mem ihx ihy
    | smul s x hx ih =>
      simpa only [Prod.smul_mk, smul_zero] using T.smul_mem s ih
  apply top_unique
  rintro ⟨s, n⟩ _
  simpa only [Prod.mk_add_mk, zero_add, add_zero] using T.add_mem (hfirst s) (hsecond n)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SemilinearMap.BundleCycles
