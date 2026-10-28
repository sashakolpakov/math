import Mathlib

/-! # Homology Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.HomologyFiniteness

noncomputable section

open _root_.CategoryTheory

universe u v w

/-- Cycles form a submodule of the finite term and homology is their quotient. -/
theorem homology_finite {R : Type u} [Ring R] [IsNoetherianRing R]
    {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (i : ι)
    [Module.Finite R (K.X i)] : Module.Finite R (K.homology i) := by
  let : Module.Finite R (K.cycles i) :=
    Module.Finite.of_injective (K.iCycles i).hom
      ((ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance)
  exact Module.Finite.of_surjective (K.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.HomologyFiniteness
