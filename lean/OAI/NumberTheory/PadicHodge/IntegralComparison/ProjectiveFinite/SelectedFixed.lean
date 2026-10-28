import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueDataAnnihilation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueFixed
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.SectionEvaluation

/-! # Selected Fixed -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.SelectedFixed

noncomputable section

/-! Fixedness of the actual selected finite residue follows from the
actual point ideal annihilation and the selected fiber component. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra IntegralComparison.Finite.FlatCoefficientSections.quotientAlgebra IntegralComparison.Finite.FlatCoefficientSections.coefficientAlgebra IntegralComparison.Finite.FlatCoefficientSections.ambientAlgebra
variable (X Y : Over (Spec (CommRingCat.of R))) [Nonempty X.left] (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
  [SmoothOfRelativeDimension g X.hom]
  (s₀ : Spec (CommRingCat.of R) ⟶ Y.left) (hbase : s₀ ≫ Y.hom = 𝟙 _)
  (B : ℕ) (hB : n+2≤B) (U : (Projective.IntrinsicOverlap.Intrinsic.space R (n+1)).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data X i (s₀ ≫ f.left) g U hU)
  (hgood : FiniteEtale.TraceBasis.Good R Y X f (i.left ⁻¹ᵁ U))
  (z : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U)
  (hz :
    letI : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X (i.left ⁻¹ᵁ U)
    letI : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))
    letI := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains
    letI : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) := hgood.2.2
    letI : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) := f.left.finite_app _ hgood.1
    letI : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
      AffineOpen.DeRhamTrace.sectionEtale R Y X f (i.left ⁻¹ᵁ U) hgood.1
    (1 ⊗ₜ[IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U] z : R ⊗[IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U] IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) =
      FiniteEtale.FiberSectionTrace.component (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) R
        (IntegralComparison.Finite.SectionEvaluation.evaluation R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains))
  (he :
    letI : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X (i.left ⁻¹ᵁ U)
    letI : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))
    letI := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains
    IntegralComparison.Finite.SectionEvaluation.evaluation R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains z = 1)

abbrev fixed := by
  letI : Subsingleton (Spec (CommRingCat.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  let hsec := FiniteEtale.SectionUnit.section_over X Y f i s₀ hbase
  let hsX := SectionEvaluationNaturality.image_retraction R Y X f s₀ hbase
  letI : IsClosedImmersion (s₀ ≫ f.left) :=
    isClosedImmersion_of_comp_eq_id (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (s₀ ≫ f.left) hsec
  let hpoint : ((s₀ ≫ f.left) ≫ i.left) ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom = 𝟙 _ :=
    (Category.assoc _ _ _).trans hsec
  letI : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X (i.left ⁻¹ᵁ U)
  letI : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))
  letI : Algebra R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) U
  letI := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains
  let ε := IntegralComparison.Finite.SectionEvaluation.evaluation R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains
  let r := ProjectivePoint.ResidueData.residue X i (s₀ ≫ f.left) hsX B hB U hU D
  have hlift (v : R) :
      algebraMap (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) R (i.left.app U (algebraMap R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) v)) = v := by
    change Intrinsic.SectionEvaluation.evaluation R X (s₀ ≫ f.left) hsX
      (i.left ⁻¹ᵁ U) D.contains (i.left.app U (algebraMap R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) v)) = v
    rw [SectionEvaluationNaturality.pullback R X (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) i (s₀ ≫ f.left) hsX U D.contains]
    exact (Intrinsic.SectionEvaluation.evaluation R (Projective.IntrinsicOverlap.Intrinsic.model R (n+1))
      ((s₀ ≫ f.left) ≫ i.left) hpoint U D.contains).commutes v
  have hscalar (a : Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U))
      (ha : algebraMap (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) R (i.left.app U a) = 0) : a • r = 0 := by
    have heval := SectionEvaluationNaturality.pullback R X (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) i
      (s₀ ≫ f.left) hsX U D.contains a
    change Intrinsic.SectionEvaluation.evaluation R X (s₀ ≫ f.left) hsX
      (i.left ⁻¹ᵁ U) D.contains (i.left.app U a) = 0 at ha
    have hzero : Intrinsic.SectionEvaluation.evaluation R (Projective.IntrinsicOverlap.Intrinsic.model R (n+1))
        ((s₀ ≫ f.left) ≫ i.left) hpoint U D.contains a = 0 := heval.symm.trans ha
    have hmem : a ∈ ((s₀ ≫ f.left) ≫ i.left).ker.ideal ⟨U,hU⟩ := by
      rw [← Intrinsic.SectionEvaluation.kernel R (Projective.IntrinsicOverlap.Intrinsic.model R (n+1))
        ((s₀ ≫ f.left) ≫ i.left) hpoint U D.contains hU]
      exact hzero
    exact ProjectivePoint.ResidueDataAnnihilation.annihilated X i (s₀ ≫ f.left) hsX B hB U hU D a hmem
  exact Principal.FiniteEtaleResidueFixed.fixed R X Y f i.left U hU hgood g
    (PrincipalPoint.Fraction.family U D.parameters) D.codimension (D.codimension+g)
    ε (algebraMap R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)) hlift
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) 1 (fun a => i.left.app U (D.parameters a)))
    r hscalar z hz he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.SelectedFixed
