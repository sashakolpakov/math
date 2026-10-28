import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Module Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ModuleHomology

/-! Homology of a module complex is finite whenever its term in that degree is finite. -/

open _root_.CategoryTheory

universe u v w

variable (R : Type u) [CommRing R]

theorem finite (S : ShortComplex (ModuleCat.{v} R)) [Finite S.X₂] : Finite S.homology := by
  let : Finite S.cycles := Finite.of_injective S.iCycles
    ((ModuleCat.mono_iff_injective S.iCycles).mp inferInstance)
  exact Finite.of_surjective S.homologyπ ((ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance)

theorem complex {ι : Type w} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{v} R) c)
    (i : ι) [Finite (K.X i)] : Finite (K.homology i) := by
  let : Finite (K.sc i).X₂ := inferInstanceAs (Finite (K.X i))
  exact finite R (K.sc i)

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ModuleHomology
