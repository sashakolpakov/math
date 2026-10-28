import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RingTheory.Noetherian.Basic

/-! # Finite Homology Of Term -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteHomologyOfTerm

/-! A finite term of a complex over a Noetherian ring has finite homology. -/

open _root_.CategoryTheory
universe u v

theorem moduleFinite_homology_of_moduleFinite_term
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (n : ι)
    [Module.Finite R (K.X n)] : Module.Finite R (K.homology n) := by
  let : Module.Finite R (K.cycles n) :=
    Module.Finite.of_injective (K.iCycles n).hom
      ((ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance)
  exact Module.Finite.of_surjective (K.homologyπ n).hom
    ((ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance)

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteHomologyOfTerm
