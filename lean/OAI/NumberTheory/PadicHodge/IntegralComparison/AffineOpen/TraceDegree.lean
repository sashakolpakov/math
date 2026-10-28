import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.PullbackUnit

/-! # Trace Degree -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.TraceDegree.DeRham

noncomputable section

/-! On every genuine finite étale affine chart, pullback followed by
the native de Rham trace is multiplication by the coefficient degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] DeRhamTrace.sectionAlgebra DeRhamTrace.sectionTower DeRhamTrace.polynomialSource DeRhamTrace.polynomialTower
  DeRhamTrace.polynomialBaseTower DeRhamTrace.sourceEtale

universe u v

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] (U : Y.left.Opens) [Fact (IsAffineOpen U)]
  (σ : Type u) [Fintype σ] [LinearOrder σ]
  [Algebra (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U)]
  [IsScalarTower R (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U)]
  [Algebra.Etale (MvPolynomial σ R) (DeRhamTrace.targetRing R Y U)]
  {ι : Type v} [Fintype ι] (b : Module.Basis ι (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U))
  (d : ℕ) (hd : Algebra.trace (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U) 1 = (d : DeRhamTrace.targetRing R Y U))

include hd in
theorem ordinary_pullback_trace_of_degree :
    IntrinsicDeRham.PullbackUnit.Intrinsic.ordinaryMap R X Y f U ≫
        IntegralComparison.Etale.DeRhamTrace.trace R (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U) σ b =
      d • 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R (DeRhamTrace.targetRing R Y U)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro ω
  change IntegralComparison.Etale.DeRhamTraceCoordinates.formTrace R (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U) σ b n
      (OrdinaryFormScalars.Ordinary.map R (DeRhamTrace.targetRing R Y U) (DeRhamTrace.sourceRing R X Y f U) n ω) = d • ω
  have h := IntegralComparison.Etale.DeRhamTraceCoordinates.trace_projection_formula R (DeRhamTrace.targetRing R Y U)
    (DeRhamTrace.sourceRing R X Y f U) σ b n 1 ω
  simpa only [one_smul, hd, Nat.cast_smul_eq_nsmul] using h

include hd in
theorem pullback_trace_of_degree :
    IntrinsicDeRham.PullbackUnit.Intrinsic.sectionMap R X Y f U ≫ DeRhamTrace.map R X Y f U σ b =
      d • 𝟙 (IntrinsicDeRham.SectionUnit.Intrinsic.sections R Y U) := by
  let : IsIso (IntrinsicDeRham.SectionUnit.Intrinsic.unit R Y U) := IntrinsicDeRham.SectionUnit.Intrinsic.unit_isIso R Y U Fact.out σ
  apply (cancel_epi (IntrinsicDeRham.SectionUnit.Intrinsic.unit R Y U)).mp
  rw [← Category.assoc, IntrinsicDeRham.PullbackUnit.Intrinsic.unit_square, Category.assoc,
    DeRhamTrace.map_unit, ← Category.assoc, ordinary_pullback_trace_of_degree R X Y f U σ b d hd]
  simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.TraceDegree.DeRham
