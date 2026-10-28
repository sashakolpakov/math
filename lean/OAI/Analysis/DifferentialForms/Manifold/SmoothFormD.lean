import OAI.Analysis.DifferentialForms.Manifold.Presheaf
import OAI.Analysis.DifferentialForms.Manifold.Gluing
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Smooth Form D -/

namespace OAI.Analysis.DifferentialForms.Manifold.SmoothFormD

noncomputable section

/-!
The actual module-valued sheaf of smooth complex-valued real differential
forms on the ordinary open subsets of a real normed space. The sheaf axiom
is proved from the previously constructed unique smooth gluing operation.
The natural exterior derivative is then a morphism of these sheaves.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u

/-- Expose the usual additive structure through the topological-sheaf wrapper. -/
instance complexModuleSheafPreadditive (X : TopCat.{u}) :
    Preadditive (TopCat.Sheaf (ModuleCat.{u} ℂ) X) :=
  inferInstanceAs (Preadditive
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} ℂ)))

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual smooth-form presheaf satisfies mathlib's categorical sheaf axiom. -/
theorem smoothFormPresheaf_isSheaf (n : ℕ) : (Manifold.Presheaf.smoothFormPresheaf E n).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (Manifold.Presheaf.smoothFormPresheaf E n)).2
  intro ι U forms hcompat
  have hlocal : OpenD.SmoothOpenForm.Compatible forms := by
    apply (OpenD.SmoothOpenForm.compatible_iff_restrict forms).2
    intro i j
    exact hcompat i j
  obtain ⟨form, hform, huniq⟩ := OpenD.SmoothOpenForm.existsUnique_glue_iSup forms hlocal
  exact ⟨form, hform, huniq⟩

/-- The genuine sheaf of smooth complex-valued real n-forms. -/
def smoothFormSheaf (n : ℕ) : TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of E) where
  obj := Manifold.Presheaf.smoothFormPresheaf E n
  property := smoothFormPresheaf_isSheaf E n

@[simp]
theorem smoothFormSheaf_presheaf (n : ℕ) :
    (smoothFormSheaf E n).presheaf = Manifold.Presheaf.smoothFormPresheaf E n := rfl

/-- The already-proved natural exterior derivative is a sheaf morphism. -/
def smoothFormSheafD (n : ℕ) : smoothFormSheaf E n ⟶ smoothFormSheaf E (n + 1) :=
  ObjectProperty.homMk (Manifold.Presheaf.smoothFormPresheafD E n)

/-- Exterior differentiation squares to zero as a sheaf morphism. -/
theorem smoothFormSheafD_squared (n : ℕ) :
    smoothFormSheafD E n ≫ smoothFormSheafD E (n + 1) = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  exact Manifold.Presheaf.smoothFormPresheafD_squared E n

end

end OAI.Analysis.DifferentialForms.Manifold.SmoothFormD
