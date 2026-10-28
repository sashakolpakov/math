import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Refinement

/-! # Refinement -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Refinement

noncomputable section

/-!
# ChernClass: cover refinement preserves the rational singular comparison

The proof uses the naturality of actual global singular restrictions and of
the evaluation of locally constant functions as singular zero-cochains.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I J : Type} (X : TopCat.{0})
variable (U : I → Opens X) (V : J → Opens X) (r : J → I) (hr : ∀ j, V j ≤ U (r j))

/-- Global singular restrictions commute with passing to a finer cover. -/
theorem globalSingularCechColumnAugmentation_refinement (M : ModuleCat ℚ) (n : ℕ) :
    (Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U M).f n ≫
      ModuleCat.ofHom (Rational.Cech.RationalCech.cechRefinementMap (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U V r hr 0) =
    (Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X V M).f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext a
  change (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M ((Opens.toTopCat X).map
      (homOfLE (Rational.Cech.RationalCech.cechIntersection_refinement_le U V r hr a)))).f n
        (((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U M).f n c) (r ∘ a)) =
    ((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X V M).f n c) a
  rw [Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation_apply, Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation_apply]
  have h := AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp M
    ((Opens.toTopCat X).map (homOfLE (Rational.Cech.RationalCech.cechIntersection_refinement_le U V r hr a)))
    (show TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (r ∘ a)) ⟶ X from
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
  exact (ConcreteCategory.congr_hom (congrArg (fun f => f.f n) h) c).symm

/-- The augmentation to the total complex is natural under refinement. -/
theorem globalSingularCechAugmentation_refinement (M : ModuleCat ℚ) :
    Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U M ≫
      Cech.Refinement.RationalCech.cechTotalRefinement U V r hr (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) =
    Rational.CechComparison.RationalCech.globalSingularCechAugmentation X V M := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, Rational.CechComparison.RationalCech.globalSingularCechAugmentation_f,
    Rational.CechComparison.RationalCech.globalSingularCechAugmentation_f]
  change ((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U M).f n ≫
      Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) 0 n n _) ≫ _ =
    (Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X V M).f n ≫
      Rational.Cech.RationalCech.cechTotalInclusion V (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) 0 n n _
  rw [Category.assoc, Cech.Refinement.RationalCech.cechTotalInclusion_refinement, ← Category.assoc]
  exact congrArg (fun f => f ≫
    Rational.Cech.RationalCech.cechTotalInclusion V (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) 0 n n (Nat.zero_add n))
    (globalSingularCechColumnAugmentation_refinement X U V r hr M n)

/-- Evaluation of locally constant Cech cochains commutes with refinement. -/
theorem locallyConstantCechToTotal_refinement :
    Cech.Obj.RationalCech.locallyConstantCechToTotal X U ≫
      Cech.Refinement.RationalCech.cechTotalRefinement U V r hr (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) =
    Rational.Cech.RationalCech.cechRefinement (Cech.Obj.RationalCech.locallyConstantPresheaf X) U V r hr ≫ Cech.Obj.RationalCech.locallyConstantCechToTotal X V := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (ModuleCat.ofHom (Cech.Obj.RationalCech.locallyConstantCechEvaluation X U n) ≫
      Rational.Cech.RationalCech.cechTotalInclusion U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) n 0 n _) ≫ _ =
    ModuleCat.ofHom (Rational.Cech.RationalCech.cechRefinementMap (Cech.Obj.RationalCech.locallyConstantPresheaf X) U V r hr n) ≫
      (ModuleCat.ofHom (Cech.Obj.RationalCech.locallyConstantCechEvaluation X V n) ≫
        Rational.Cech.RationalCech.cechTotalInclusion V (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) n 0 n _)
  rw [Category.assoc, Cech.Refinement.RationalCech.cechTotalInclusion_refinement, ← Category.assoc, ← Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact (Cech.Refinement.RationalCech.cechCoefficientMap_refinement U V r hr (Cech.Obj.RationalCech.locallyConstantSingularAugmentation X) n c).symm

/-- Refinement followed by inverse global comparison is the original inverse comparison. -/
theorem singularCechCohomologyIso_inv_refinement
    (hU : ∀ x : X, ∃ i, x ∈ U i) (hV : ∀ x : X, ∃ j, x ∈ V j) (n : ℕ) :
    HomologicalComplex.homologyMap
        (Cech.Refinement.RationalCech.cechTotalRefinement U V r hr (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) n ≫
      (Rational.CechComparison.RationalCech.singularCechCohomologyIso X V hV n).inv =
    (Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU n).inv := by
  apply (cancel_epi (Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU n).hom).mp
  rw [← Category.assoc, Rational.CechComparison.RationalCech.singularCechCohomologyIso_hom,
    ← HomologicalComplex.homologyMap_comp, globalSingularCechAugmentation_refinement]
  exact (Rational.CechComparison.RationalCech.singularCechCohomologyIso X V hV n).hom_inv_id.trans
    (Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU n).hom_inv_id.symm

/-- The locally constant Cech-to-singular map is invariant under cover refinement. -/
theorem cechCohomologyToSingular_refinement
    (hU : ∀ x : X, ∃ i, x ∈ U i) (hV : ∀ x : X, ∃ j, x ∈ V j) (n : ℕ) :
    HomologicalComplex.homologyMap (Rational.Cech.RationalCech.cechRefinement (Cech.Obj.RationalCech.locallyConstantPresheaf X) U V r hr) n ≫
      Cech.Obj.RationalCech.cechCohomologyToSingular X V hV n = Cech.Obj.RationalCech.cechCohomologyToSingular X U hU n := by
  unfold Cech.Obj.RationalCech.cechCohomologyToSingular
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← locallyConstantCechToTotal_refinement, HomologicalComplex.homologyMap_comp,
    Category.assoc, singularCechCohomologyIso_inv_refinement X U V r hr hU hV n]

/-- A rational Cech cocycle and its restriction give the same singular class. -/
theorem singularClassOfCechCocycle_refinement
    (hU : ∀ x : X, ∃ i, x ∈ U i) (hV : ∀ x : X, ∃ j, x ∈ V j) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) n) :
    Cech.Obj.RationalCech.singularClassOfCechCocycle X V hV n
        (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (Rational.Cech.RationalCech.cechRefinement (Cech.Obj.RationalCech.locallyConstantPresheaf X) U V r hr) n c) =
      Cech.Obj.RationalCech.singularClassOfCechCocycle X U hU n c := by
  unfold Cech.Obj.RationalCech.singularClassOfCechCocycle
  rw [← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  exact ConcreteCategory.congr_hom
    (cechCohomologyToSingular_refinement X U V r hr hU hV n)
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) n c)

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Refinement
