import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CoefficientNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HypercohomologyAdditive

/-! # De Rham Pullback Linear -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DeRhamPullbackLinear

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint
open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

/-! # Complex linearity of actual pullback on the original de Rham cohomology

The unchanged complex constant comparison is bijective. Naturality in actual
coefficient maps therefore proves complex linearity of genuine de Rham pullback.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

variable {X Y : Over (Spec (.of ℂ))}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

/-- The actual original de Rham pullback is additive. -/
def originalDeRhamHypercohomologyPullbackAddHom (f : X ⟶ Y) (n : ℤ) :
    H_dR^n(Y) →+ H_dR^n(X) :=
  (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (InverseImageMap.originalDeRhamInverseImagePullback f) n).comp
    (HypercohomologyAdditive.originalHypercohomologyPullbackAddHom f Ω•(Y) n)

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom] in
/-- Actual constant pullback commutes with original complex coefficient multiplication. -/
theorem originalComplexConstantHypercohomologyPullback_scalar (f : X ⟶ Y) (n : ℤ)
    (c : ℂ) (α : ComplexPoint.Basic.ComplexSchemePoint.ComplexConstantCohomology Y n) :
    ConstantDeRhamNaturality.originalComplexConstantHypercohomologyPullback f n
        (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap Y (ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt Y c) n α) =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X c) n
        (ConstantDeRhamNaturality.originalComplexConstantHypercohomologyPullback f n α) := by
  let β := HypercohomologyPullback.originalHypercohomologyPullback f (ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt Y) n α
  have hn := HypercohomologyPullback.originalHypercohomologyPullback_naturality f (ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt Y c) n α
  have hc : (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.map
        (ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt Y c) ≫ (ConstantDeRhamNaturality.originalComplexComplexInverseImageIso f).hom =
      (ConstantDeRhamNaturality.originalComplexComplexInverseImageIso f).hom ≫ ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X c :=
    CoefficientNaturality.originalCoefficientComplexInverseImageIso_naturality f
      (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft c))
  exact (congrArg (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ConstantDeRhamNaturality.originalComplexComplexInverseImageIso f).hom n) hn).trans
    ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply X
      ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.map (ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt Y c))
      (ConstantDeRhamNaturality.originalComplexComplexInverseImageIso f).hom n β).symm.trans
        ((congrArg (fun g ↦ ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X g n β) hc).trans
          (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply X (ConstantDeRhamNaturality.originalComplexComplexInverseImageIso f).hom
            (ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X c) n β)))

/-- Genuine pullback of the unchanged original de Rham cohomology is complex linear. -/
theorem originalDeRhamHypercohomologyPullback_smul (f : X ⟶ Y) (n : ℤ)
    (c : ℂ) (α : H_dR^n(Y)) :
    FilteredPullback.originalDeRhamHypercohomologyPullback f n (c • α) =
      c • FilteredPullback.originalDeRhamHypercohomologyPullback f n α := by
  let eY := ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv Y n
  let eX := ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n
  obtain ⟨β, rfl⟩ := eY.surjective α
  exact (congrArg (FilteredPullback.originalDeRhamHypercohomologyPullback f n)
      (CMComparisonTo.complexComparison_scalar Y n c β).symm).trans
    ((ConstantDeRhamNaturality.originalDeRhamHypercohomologyPullback_constantComparison f n
      (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap Y (ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt Y c) n β)).trans
        ((congrArg eX (originalComplexConstantHypercohomologyPullback_scalar f n c β)).trans
          ((CMComparisonTo.complexComparison_scalar X n c
            (ConstantDeRhamNaturality.originalComplexConstantHypercohomologyPullback f n β)).trans
              (congrArg (c • ·)
                (ConstantDeRhamNaturality.originalDeRhamHypercohomologyPullback_constantComparison f n β).symm))))

/-- The actual pullback on the original geometric de Rham cohomology, bundled linearly. -/
def originalDeRhamHypercohomologyPullbackLinear (f : X ⟶ Y) (n : ℤ) :
    H_dR^n(Y) →ₗ[ℂ] H_dR^n(X) :=
  { originalDeRhamHypercohomologyPullbackAddHom f n with
    map_smul' := originalDeRhamHypercohomologyPullback_smul f n }

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DeRhamPullbackLinear
