import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic

/-! # Homology Sequences -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.HomologySequences

noncomputable section

/-! Finiteness propagates through exact sequences and through the homology sequence of actual module complexes. -/

open _root_.CategoryTheory

universe u v w t

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type t} [AddCommGroup P] [Module R P]

theorem finite_middle_of_exact (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hex : Function.Exact f g) [Module.Finite R M] [Module.Finite R P] : Module.Finite R N := by
  apply Module.Finite.of_exact (f := f) (g := g.rangeRestrict) _ g.surjective_rangeRestrict
  intro y
  constructor
  · intro hy
    exact (hex y).mp (congrArg Subtype.val hy)
  · intro hy
    exact Subtype.ext ((hex y).mpr hy)

theorem finite_homology_of_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{v} R) ℕ)) (hS : S.ShortExact) (q : ℕ)
    [Module.Finite R (S.X₂.homology q)] [Module.Finite R (S.X₁.homology (q + 1))] :
    Module.Finite R (S.X₃.homology q) := by
  have hex := hS.homology_exact₃ q (q + 1) rfl
  apply finite_middle_of_exact R (HomologicalComplex.homologyMap S.g q).hom
    (hS.δ q (q + 1) rfl).hom
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hex

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.HomologySequences
