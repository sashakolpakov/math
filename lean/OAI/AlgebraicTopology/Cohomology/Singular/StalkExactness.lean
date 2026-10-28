import OAI.AlgebraicTopology.Cohomology.Singular.LocalPrimitives
import OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt
import OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf

/-! # Stalk Exactness -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.StalkExactness

noncomputable section

/-!
# Local exactness of the genuine singular cochain complex

The presheaf differential here is the actual singular coboundary on each open
subspace. Its positive-degree stalk exactness is deduced from verified local
singular primitives and the genuine filtered-colimit description of stalks.
For real normed manifold charts the required local contractibility is proved,
not supplied as additional topological data.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open _root_.TopCat.Presheaf

variable {R : Type} [Ring R]

/-- The actual singular cochain presheaf has exact positive-degree stalk
complexes on every strongly locally contractible space. -/
theorem singularStalkComplex_exactAt_succ
    (A : ModuleCat.{0} R) (X : TopCat.{0}) [StronglyLocallyContractibleSpace X]
    (x : X) (n : ℕ) :
    (((stalkFunctor (ModuleCat.{0} R) x).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A X)).ExactAt (n + 1) := by
  apply StalkExactnessAt.stalkComplex_exactAt_succ_of_local_primitives
  intro U hxU c hc
  let z : Representatives.singularCocycles A (TopCat.of U) (n + 1) :=
    ⟨c, (Representatives.mem_cochainCocycles_iff _ _ _).mpr hc⟩
  obtain ⟨V, hxV, hVU, b, hb⟩ := LocalPrimitives.exists_local_singularPrimitive A X U x hxU n z
  exact ⟨V, hxV, homOfLE hVU, b, hb⟩

/-- Positive cohomology of the actual singular stalk complex vanishes. -/
theorem isZero_singularStalkCohomology_succ
    (A : ModuleCat.{0} R) (X : TopCat.{0}) [StronglyLocallyContractibleSpace X]
    (x : X) (n : ℕ) :
    IsZero ((((stalkFunctor (ModuleCat.{0} R) x).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A X)).homology
      (n + 1)) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact singularStalkComplex_exactAt_succ A X x n

/-- Real normed manifold charts alone imply positive-degree exactness of the
actual singular stalk complex; no extra local topology hypothesis is used. -/
theorem singularStalkComplex_exactAt_succ_of_chartedSpace
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ModuleCat.{0} R) (X : TopCat.{0}) [ChartedSpace E X]
    (x : X) (n : ℕ) :
    (((stalkFunctor (ModuleCat.{0} R) x).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A X)).ExactAt (n + 1) := by
  let := ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace E X
  exact singularStalkComplex_exactAt_succ A X x n

end

end OAI.AlgebraicTopology.Cohomology.Singular.StalkExactness
