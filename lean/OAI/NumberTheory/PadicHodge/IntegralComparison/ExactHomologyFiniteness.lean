import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Finsupp

/-! # Exact Homology Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ExactHomologyFiniteness

noncomputable section

/-! Finite cohomology is preserved by the actual short exact sequence of module complexes. -/

open _root_.CategoryTheory

universe u v

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

theorem middle (S : ShortComplex (ModuleCat.{v} R)) (hS : S.Exact)
    [Module.Finite R S.X₁] [Module.Finite R S.X₃] : Module.Finite R S.X₂ := by
  let : Module.Finite R (LinearMap.ker S.g.hom) := by
    rw [← hS.moduleCat_range_eq_ker]
    infer_instance
  let : Module.Finite R (S.X₂ ⧸ LinearMap.ker S.g.hom) :=
    Module.Finite.equiv S.g.hom.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker S.g.hom)

theorem homology (S : ShortComplex (CochainComplex (ModuleCat.{v} R) ℕ)) (hS : S.ShortExact) (i : ℕ)
    [Module.Finite R (S.X₁.homology i)] [Module.Finite R (S.X₃.homology i)] :
    Module.Finite R (S.X₂.homology i) := by
  let : Module.Finite R (S.map (HomologicalComplex.homologyFunctor _ _ i)).X₁ :=
    inferInstanceAs (Module.Finite R (S.X₁.homology i))
  let : Module.Finite R (S.map (HomologicalComplex.homologyFunctor _ _ i)).X₃ :=
    inferInstanceAs (Module.Finite R (S.X₃.homology i))
  exact middle R (S.map (HomologicalComplex.homologyFunctor _ _ i)) (hS.homology_exact₂ i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ExactHomologyFiniteness
