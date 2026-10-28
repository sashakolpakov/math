import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Descent
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.IntegralRefinement
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Refinement

/-! # Integral Cech Representative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralCechRepresentative

noncomputable section

/-! Positive multiples of rational Betti two-classes have actual integral Cech representatives. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Refinement.RationalCech

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

def integerCechRationalCocycle (n : ℕ) (g : Cech.IntegralRefinement.IntegerCechCochain U n)
    (hg : Cech.IntegralRefinement.integerCechDelta U n g = 0) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) n :=
  ⟨Cech.IntegralRefinement.integerCechRationalize U n g, by
    erw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff, Rational.Cech.RationalCech.cechComplex_d]
    erw [← Cech.IntegralRefinement.integerCechRationalize_delta, hg, map_zero]⟩

theorem singularClassOfCechCocycle_smul (hU : ∀ x : X, ∃ i, x ∈ U i)
    (n : ℕ) (r : ℚ) (k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) n) :
    Cech.Obj.RationalCech.singularClassOfCechCocycle X U hU n (r • k) =
      r • Cech.Obj.RationalCech.singularClassOfCechCocycle X U hU n k := by
  unfold Cech.Obj.RationalCech.singularClassOfCechCocycle
  rw [map_smul, map_smul]

theorem exists_integralCechTwoRepresentative [CompactSpace X] [NormalSpace X]
    [StronglyLocallyContractibleSpace X] [LocallyPathConnectedSpace X]
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 2) :
    ∃ (I : Type) (_ : Finite I) (U : I → Opens X) (hU : ∀ x, ∃ i, x ∈ U i)
      (N : ℕ), 0 < N ∧ ∃ (g : Cech.IntegralRefinement.IntegerCechCochain U 2) (hg : Cech.IntegralRefinement.integerCechDelta U 2 g = 0),
      Cech.Obj.RationalCech.singularClassOfCechCocycle X U hU 2 (integerCechRationalCocycle U 2 g hg) =
        (N : ℚ) • a := by
  obtain ⟨I, U, hU, k, hk⟩ := Cech.Descent.exists_rationalCechTwoRepresentative a
  have hclosed : Rational.Cech.RationalCech.cechDelta (Cech.Obj.RationalCech.locallyConstantPresheaf X) U 2 k.val = 0 := by
    have h := k.property
    erw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff, Rational.Cech.RationalCech.cechComplex_d] at h
    exact h
  obtain ⟨r, N, hN, g, hg, he⟩ := Cech.IntegralRefinement.exists_integral_cech_refinement U hU 2 k.val hclosed
  refine ⟨r.charts, inferInstance, r.cover, r.covers, N, hN, g, hg, ?_⟩
  have he' : integerCechRationalCocycle r.cover 2 g hg = (N : ℚ) •
      AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (Rational.Cech.RationalCech.cechRefinement (Cech.Obj.RationalCech.locallyConstantPresheaf X)
        U r.cover Subtype.val r.subset) 2 k := by
    apply Subtype.ext
    exact he
  rw [he', singularClassOfCechCocycle_smul,
    Singular.Refinement.RationalCech.singularClassOfCechCocycle_refinement X U r.cover Subtype.val r.subset hU r.covers, hk]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralCechRepresentative
