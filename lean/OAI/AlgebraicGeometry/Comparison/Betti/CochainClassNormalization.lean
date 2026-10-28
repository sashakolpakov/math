import OAI.AlgebraicGeometry.Comparison.Betti.CochainClasses
import OAI.AlgebraicTopology.Cohomology.Singular.Representatives

/-! # Cochain Class Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CochainClassNormalization.Homology

noncomputable section

/-! The adjacent-degree cocycle class used by the derived comparison is
the original cochain quotient class of the identical cocycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {R : Type} [Ring R] (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)

theorem cochainClass_eq_native (z : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K n) :
    CochainClasses.Homology.cochainClass K n z.val ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff K n z.val).1 z.property) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K n z := by
  let e := K.isoSc' (n - 1) n (n + 1) (by cases n <;> simp) (CochainComplex.next ℕ n)
  have h := Module.HomologyClasses.homologyClass_naturality e.inv z.val
    ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff K n z.val).1 z.property)
  change ShortComplex.homologyMap e.inv (Module.HomologyClasses.homologyClass _ z.val _) = _
  rw [h, Module.HomologyClasses.homologyClass_quotient]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.CochainClassNormalization.Homology
