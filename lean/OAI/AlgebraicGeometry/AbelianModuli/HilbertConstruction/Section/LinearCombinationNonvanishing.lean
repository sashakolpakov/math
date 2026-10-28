import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.NonvanishingAddition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ScalarSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange

/-! # Linear Combination Nonvanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A nonvanishing finite linear combination detects a nonvanishing summand, including for linear combinations of pulled-back sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem Line.Bundles.LineBundle.mem_sectionNonvanishing_sum
    {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) {ι : Type v} (I : Finset ι)
    (s : ι → (Line.Bundles.structureModule X ⟶ L.sheaf)) (x : X) :
    x ∈ Ample.LineBundles.sectionNonvanishing (∑ i ∈ I, s i) → ∃ i ∈ I, x ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  classical
  refine Finset.induction_on I ?_ ?_
  · intro hx
    rw [Finset.sum_empty, L.sectionNonvanishing_zero] at hx
    exact False.elim hx
  · intro a J ha ih hx
    rw [Finset.sum_insert ha] at hx
    rcases L.sectionNonvanishing_add_le _ _ hx with hax | hJx
    · exact ⟨a, Finset.mem_insert_self a J, hax⟩
    · obtain ⟨i, hi, hix⟩ := ih hJx
      exact ⟨i, Finset.mem_insert_of_mem hi, hix⟩

theorem Section.LinearCombinationNonvanishing.coefficient_linearCombination_nonvanishing
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X)
    {ι : Type v} (I : Finset ι) (c : ι → K) (s : ι → (Line.Bundles.structureModule X ⟶ L.sheaf)) (x : X)
    (hx : x ∈ Ample.LineBundles.sectionNonvanishing (∑ i ∈ I, Coefficient.ScalarSections.coefficientScalarSection p (c i) (s i))) :
    ∃ i ∈ I, x ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  obtain ⟨i, hi, hix⟩ := L.mem_sectionNonvanishing_sum I (fun i => Coefficient.ScalarSections.coefficientScalarSection p (c i) (s i)) x hx
  exact ⟨i, hi, Coefficient.ScalarSections.coefficientScalarSection_nonvanishing_le p L (c i) (s i) hix⟩

theorem Section.LinearCombinationNonvanishing.pulledBack_linearCombination_nonvanishing
    {K : Type u} [Field K] {X Y : Scheme.{u}} (a : Y ⟶ X) (p : Y ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X)
    {ι : Type v} (I : Finset ι) (c : ι → K) (s : ι → (Line.Bundles.structureModule X ⟶ L.sheaf)) (y : Y)
    (hy : y ∈ Ample.LineBundles.sectionNonvanishing (∑ i ∈ I, Coefficient.ScalarSections.coefficientScalarSection p (c i) (Ample.LineBundles.pullbackSection a (s i)))) :
    ∃ i ∈ I, a y ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  obtain ⟨i, hi, hiy⟩ := Section.LinearCombinationNonvanishing.coefficient_linearCombination_nonvanishing p (L.pullback a) I c
    (fun i => Ample.LineBundles.pullbackSection a (s i)) y hy
  exact ⟨i, hi, (congrArg (fun U : Y.Opens => y ∈ U)
    (LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange a L (s i))).mp hiy⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
