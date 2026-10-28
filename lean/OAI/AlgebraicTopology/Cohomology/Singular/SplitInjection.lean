import OAI.AlgebraicTopology.Cohomology.Singular.Coefficients
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.EpiMono

/-! # Split Injection -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SplitInjection

noncomputable section

/-!
# Split coefficient maps induce injections on genuine singular cohomology

A retraction of a coefficient homomorphism is transported through the actual
singular-cochain and homology constructions. Thus a split injection of modules
induces an injection on singular cohomology in every degree, for every space.
No finiteness condition on the space or scalar-extension theorem is needed.
-/

open _root_.CategoryTheory

variable {R : Type} [Ring R] {M N : ModuleCat.{0} R}

/-- A chosen coefficient retraction gives a chosen retraction on singular
cohomology. -/
def coefficientSplitMono (f : M ⟶ N) (r : N ⟶ M)
    (h : f ≫ r = 𝟙 M) (X : TopCat.{0}) (n : ℕ) :
    SplitMono (Coefficients.coefficientMap f X n) where
  retraction := Coefficients.coefficientMap r X n
  id := by
    rw [← Coefficients.coefficientMap_comp, h, Coefficients.coefficientMap_id]

/-- The induced coefficient retraction is a left inverse on cohomology classes. -/
theorem coefficientMap_leftInverse_of_split (f : M ⟶ N) (r : N ⟶ M)
    (h : f ≫ r = 𝟙 M) (X : TopCat.{0}) (n : ℕ) :
    Function.LeftInverse (Coefficients.coefficientMap r X n) (Coefficients.coefficientMap f X n) := by
  intro x
  have hid := (coefficientSplitMono f r h X n).id
  have hx := congrArg (fun k : Basic.singularCohomology M X n ⟶
      Basic.singularCohomology M X n => k x) hid
  simpa only [ModuleCat.comp_apply, ModuleCat.id_apply,
    coefficientSplitMono] using hx

/-- A split coefficient homomorphism induces an injective singular-cohomology map. -/
theorem coefficientMap_injective_of_split (f : M ⟶ N) (r : N ⟶ M)
    (h : f ≫ r = 𝟙 M) (X : TopCat.{0}) (n : ℕ) :
    Function.Injective (Coefficients.coefficientMap f X n) :=
  (coefficientMap_leftInverse_of_split f r h X n).injective

/-- Categorical split monomorphisms of coefficients remain split on cohomology. -/
theorem coefficientMap_isSplitMono (f : M ⟶ N) [IsSplitMono f]
    (X : TopCat.{0}) (n : ℕ) : IsSplitMono (Coefficients.coefficientMap f X n) :=
  IsSplitMono.mk' (coefficientSplitMono f (retraction f) (IsSplitMono.id f) X n)

/-- The injectivity conclusion with the categorical split-injection hypothesis. -/
theorem coefficientMap_injective_of_isSplitMono (f : M ⟶ N) [IsSplitMono f]
    (X : TopCat.{0}) (n : ℕ) : Function.Injective (Coefficients.coefficientMap f X n) :=
  coefficientMap_injective_of_split f (retraction f) (IsSplitMono.id f) X n

/-- If two singular cohomology classes become equal under a split coefficient map,
they were already equal. -/
theorem coefficientMap_eq_iff_of_split (f : M ⟶ N) (r : N ⟶ M)
    (h : f ≫ r = 𝟙 M) (X : TopCat.{0}) (n : ℕ)
    (x y : Basic.singularCohomology M X n) :
    Coefficients.coefficientMap f X n x = Coefficients.coefficientMap f X n y ↔ x = y :=
  (coefficientMap_injective_of_split f r h X n).eq_iff

end

end OAI.AlgebraicTopology.Cohomology.Singular.SplitInjection
