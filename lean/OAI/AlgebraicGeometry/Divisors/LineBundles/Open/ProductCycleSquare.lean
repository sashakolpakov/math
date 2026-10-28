import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.PreimageSupport

/-! # Product Cycle Square -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ProductCycleSquare.BundleCycles

noncomputable section

/-! The supported cycle-class comparison holds on every actual open
product chart of a morphism. All inputs describe scheme geometry and
support dimensions; the cohomological square is proved here. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

theorem openProductSupport_preimage {E X U P : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : E ⟶ X) (i : U ⟶ X) (j : P ⟶ E) (π : P ⟶ U) (hsq : j ≫ f = π ≫ i)
    (B : IrreducibleCloseds X.left) (C : IrreducibleCloseds E.left)
    (A : IrreducibleCloseds U.left) (D : IrreducibleCloseds P.left)
    (hC : (C : Set E.left) = f.left ⁻¹' (B : Set X.left))
    (hA : (A : Set U.left) = i.left ⁻¹' (B : Set X.left))
    (hD : (D : Set P.left) = j.left ⁻¹' (C : Set E.left)) :
    (D : Set P.left) = π.left ⁻¹' (A : Set U.left) := by
  rw [hD, hC, hA]
  ext z
  change f.left (j.left z) ∈ (B : Set X.left) ↔ i.left (π.left z) ∈ (B : Set X.left)
  have he := congrArg (fun k : P ⟶ X => k.left z) hsq
  exact congrArg (fun x => x ∈ (B : Set X.left)) he |>.to_iff

variable {E X U P : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    [IsIntegral E.left] [Smooth E.hom] [AlgebraicGeometry.IsNoetherian E.left]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)]
    [IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    [IsIntegral U.left] [Smooth U.hom] [AlgebraicGeometry.IsNoetherian U.left]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U)]
    [IsIntegral P.left] [Smooth P.hom] [AlgebraicGeometry.IsNoetherian P.left]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P)]
    (f : E ⟶ X) (i : U ⟶ X) [IsOpenImmersion i.left]
    (j : P ⟶ E) [IsOpenImmersion j.left] (F : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral F.left] [Smooth F.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints F)]
    (πF : P ⟶ F) (π : P ⟶ U) (hprod : IsLimit (BinaryFan.mk πF π))
    (hsq : j ≫ f = π ≫ i)
    (B : IrreducibleCloseds X.left) (C : IrreducibleCloseds E.left)
    (A : IrreducibleCloseds U.left) (D : IrreducibleCloseds P.left)
    (hC : (C : Set E.left) = f.left ⁻¹' (B : Set X.left))
    (hA : (A : Set U.left) = i.left ⁻¹' (B : Set X.left))
    (hD : (D : Set P.left) = j.left ⁻¹' (C : Set E.left))

include hprod hsq hA in
theorem schemeSupportedCycleClass_on_open_product (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (hc : Foundations.Scheme.SupportDimension.supportTranscendenceDimension C E.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension E.hom)
    (ha : Foundations.Scheme.SupportDimension.supportTranscendenceDimension A U.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension U.hom)
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D P.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension P.hom) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map j)
      (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo j C D hD) (2 * p)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
        (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo f B C hC) (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X B p hp)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map j)
      (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo j C D hD) (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass E C p hc) := by
  let : Nonempty (SupportRestriction.BundleCycles.openSupportPullback i.left B) :=
    (SupportRestriction.BundleCycles.openSupportPullback_nonempty_iff i.left B).mpr (hA ▸ A.isIrreducible.nonempty)
  let : Nonempty (SupportRestriction.BundleCycles.openSupportPullback j.left C) :=
    (SupportRestriction.BundleCycles.openSupportPullback_nonempty_iff j.left C).mpr (hD ▸ D.isIrreducible.nonempty)
  have hDP := openProductSupport_preimage f i j π hsq B C A D hC hA hD
  have hf := SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo f B C hC
  have hi := SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo i B A hA
  have hj := SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo j C D hD
  have hπ := SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo π A D hDP
  have hmap : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map j ≫ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map π ≫ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i := by
    rw [← Functor.map_comp, hsq, Functor.map_comp]
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map j)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) hj hf (2 * p)) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X B p hp)
  have hm := ConcreteCategory.congr_hom
    (CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr hmap (hf.comp hj) (hi.comp hπ) (2 * p))
    (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X B p hp)
  have h₂ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map π)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i) hπ hi (2 * p)) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X B p hp)
  have h₃ := congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map π) hπ (2 * p))
      (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportedCycleClass_open_of_support i B A hA p hp ha)
  have h₄ := SchemeCycle.PreimageSupport.BundleCycles.schemeSupportedCycleClass_projection_of_support F U P πF π hprod A D hDP p ha hd
  have h₅ := SchemeCycle.PreimageSupport.BundleCycles.schemeSupportedCycleClass_open_of_support j C D hD p hc hd
  exact h₁.trans (hm.trans (h₂.symm.trans (h₃.trans (h₄.trans h₅.symm))))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ProductCycleSquare.BundleCycles
