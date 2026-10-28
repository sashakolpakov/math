import OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet
import OAI.AlgebraicTopology.Cohomology.Singular.Functor
import OAI.AlgebraicTopology.Cohomology.Singular.Coefficients

/-! # Small Singular Cochains -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularCochains

noncomputable section

/-!
# Restriction to small singular cochains

For a family of subsets, this file restricts genuine singular cochains to the
simplices contained in one family member. Refinements induce further
restriction maps, compatible with composition and with the global restriction.
No assertion about subdivision or a quasi-isomorphism is made here.
-/

open _root_.CategoryTheory Opposite

variable {R : Type} [Ring R]
variable {ι κ ν : Type}

/-- Cochains on the actual small-singular simplicial subset. -/
abbrev smallSingularCochains (M : ModuleCat.{0} R) (X : TopCat.{0}) (U : ι → Set X) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  Cohomology.Singular.Basic.simplicialCochains (SmallSingularSet.smallSingularSubcomplex X U : SSet) M

/-- Restrict genuine singular cochains to the small singular simplices. -/
def smallSingularRestriction (M : ModuleCat.{0} R) (X : TopCat.{0}) (U : ι → Set X) :
    Cohomology.Singular.Basic.singularCochains M X ⟶ smallSingularCochains M X U :=
  Cohomology.Singular.Functor.simplicialPullback M (SmallSingularSet.smallSingularInclusion X U)

/-- Cohomology of the small-singular cochain complex. -/
abbrev smallSingularCohomology (M : ModuleCat.{0} R) (X : TopCat.{0})
    (U : ι → Set X) (n : ℕ) : ModuleCat.{0} R :=
  (smallSingularCochains M X U).homology n

/-- The cohomology map induced by restriction to small simplices. -/
def smallSingularCohomologyRestriction (M : ModuleCat.{0} R) (X : TopCat.{0})
    (U : ι → Set X) (n : ℕ) :
    Cohomology.Singular.Basic.singularCohomology M X n ⟶ smallSingularCohomology M X U n :=
  HomologicalComplex.homologyMap (smallSingularRestriction M X U) n

/-- Composition of refinement statements for families of subsets. -/
theorem smallCoverRefinement_trans {X : TopCat.{0}}
    {U : ι → Set X} {V : κ → Set X} {W : ν → Set X}
    (hUV : ∀ i, ∃ j, U i ⊆ V j) (hVW : ∀ j, ∃ k, V j ⊆ W k) :
    ∀ i, ∃ k, U i ⊆ W k := by
  intro i
  obtain ⟨j, hij⟩ := hUV i
  obtain ⟨k, hjk⟩ := hVW j
  exact ⟨k, hij.trans hjk⟩

/-- A refinement includes the corresponding small simplicial subsets. -/
def smallSingularRefinement (X : TopCat.{0}) (U : ι → Set X) (V : κ → Set X)
    (hUV : ∀ i, ∃ j, U i ⊆ V j) :
    (SmallSingularSet.smallSingularSubcomplex X U : SSet) ⟶ (SmallSingularSet.smallSingularSubcomplex X V : SSet) :=
  SSet.Subcomplex.homOfLE (SmallSingularSet.smallSingularSubcomplex_le_of_refinement X U V hUV)

@[simp, reassoc]
theorem smallSingularRefinement_inclusion (X : TopCat.{0})
    (U : ι → Set X) (V : κ → Set X) (hUV : ∀ i, ∃ j, U i ⊆ V j) :
    smallSingularRefinement X U V hUV ≫ SmallSingularSet.smallSingularInclusion X V =
      SmallSingularSet.smallSingularInclusion X U := rfl

@[simp]
theorem smallSingularRefinement_refl (X : TopCat.{0}) (U : ι → Set X) :
    smallSingularRefinement X U U (fun i => ⟨i, Set.Subset.rfl⟩) = 𝟙 _ := rfl

@[simp, reassoc]
theorem smallSingularRefinement_comp (X : TopCat.{0})
    (U : ι → Set X) (V : κ → Set X) (W : ν → Set X)
    (hUV : ∀ i, ∃ j, U i ⊆ V j) (hVW : ∀ j, ∃ k, V j ⊆ W k) :
    smallSingularRefinement X U V hUV ≫ smallSingularRefinement X V W hVW =
      smallSingularRefinement X U W (smallCoverRefinement_trans hUV hVW) := rfl

/-- Restriction of cochains along refinement of the family of small subsets. -/
def smallSingularRefinementRestriction (M : ModuleCat.{0} R) (X : TopCat.{0})
    (U : ι → Set X) (V : κ → Set X) (hUV : ∀ i, ∃ j, U i ⊆ V j) :
    smallSingularCochains M X V ⟶ smallSingularCochains M X U :=
  Cohomology.Singular.Functor.simplicialPullback M (smallSingularRefinement X U V hUV)

@[simp, reassoc]
theorem smallSingularRestriction_refinement (M : ModuleCat.{0} R) (X : TopCat.{0})
    (U : ι → Set X) (V : κ → Set X) (hUV : ∀ i, ∃ j, U i ⊆ V j) :
    smallSingularRestriction M X V ≫ smallSingularRefinementRestriction M X U V hUV =
      smallSingularRestriction M X U := by
  rw [smallSingularRestriction, smallSingularRefinementRestriction,
    ← Cohomology.Singular.Functor.simplicialPullback_comp, smallSingularRefinement_inclusion]
  rfl

@[simp]
theorem smallSingularRefinementRestriction_refl (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (U : ι → Set X) :
    smallSingularRefinementRestriction M X U U (fun i => ⟨i, Set.Subset.rfl⟩) = 𝟙 _ := by
  rw [smallSingularRefinementRestriction, smallSingularRefinement_refl,
    Cohomology.Singular.Functor.simplicialPullback_id]

@[simp, reassoc]
theorem smallSingularRefinementRestriction_comp (M : ModuleCat.{0} R) (X : TopCat.{0})
    (U : ι → Set X) (V : κ → Set X) (W : ν → Set X)
    (hUV : ∀ i, ∃ j, U i ⊆ V j) (hVW : ∀ j, ∃ k, V j ⊆ W k) :
    smallSingularRefinementRestriction M X V W hVW ≫
        smallSingularRefinementRestriction M X U V hUV =
      smallSingularRefinementRestriction M X U W (smallCoverRefinement_trans hUV hVW) := by
  rw [smallSingularRefinementRestriction, smallSingularRefinementRestriction,
    ← Cohomology.Singular.Functor.simplicialPullback_comp, smallSingularRefinement_comp]
  rfl

/-- The actual cohomology map induced by refinement. -/
def smallSingularCohomologyRefinement (M : ModuleCat.{0} R) (X : TopCat.{0})
    (U : ι → Set X) (V : κ → Set X) (hUV : ∀ i, ∃ j, U i ⊆ V j) (n : ℕ) :
    smallSingularCohomology M X V n ⟶ smallSingularCohomology M X U n :=
  HomologicalComplex.homologyMap (smallSingularRefinementRestriction M X U V hUV) n

@[simp, reassoc]
theorem smallSingularCohomologyRestriction_refinement (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (U : ι → Set X) (V : κ → Set X)
    (hUV : ∀ i, ∃ j, U i ⊆ V j) (n : ℕ) :
    smallSingularCohomologyRestriction M X V n ≫
        smallSingularCohomologyRefinement M X U V hUV n =
      smallSingularCohomologyRestriction M X U n := by
  rw [smallSingularCohomologyRestriction, smallSingularCohomologyRefinement,
    ← HomologicalComplex.homologyMap_comp, smallSingularRestriction_refinement]
  rfl

/-- Degreewise small cochains are all coefficient-valued functions on the
actual small singular simplices, with no finite-support requirement. -/
def smallSingularDegreewiseFunctionIso (M : ModuleCat.{0} R) (X : TopCat.{0})
    (U : ι → Set X) (n : ℕ) :
    (smallSingularCochains M X U).X n ≅
      ModuleCat.of R (CechCoverRows.SmallSingularSimplex X U n → M) :=
  Cohomology.Singular.Coefficients.degreewiseFunctionIso (SmallSingularSet.smallSingularSubcomplex X U : SSet) M n

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularCochains
