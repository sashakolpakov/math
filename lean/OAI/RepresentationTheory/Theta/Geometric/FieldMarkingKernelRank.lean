import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingComplexCoordinates
import OAI.RepresentationTheory.Theta.Geometric.Reference.FirstStandardCoordinates
import OAI.RepresentationTheory.Theta.Geometric.Family.EmbeddingInclusion

/-! # Field Marking Kernel Rank -/

namespace OAI.RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank

noncomputable section

section

/-! The complexification of a genuine field marking sends the literal
reference first block to the actual fiber embedding block by an invertible
embedded field matrix. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s)
    (m : let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety)
    (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

theorem fieldMarking_referenceFirst (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
    let := Family.PELCoordinates.familyPeriodScalarTower A ρ x
    (m.restrictScalars ℚ).toLinearMap.baseChange ℂ (Reference.FirstEmbedding.referenceFirstComplexInclusion P hP v) =
      Family.EmbeddingInclusion.familyEmbeddingInclusion A ρ x s hs hg hdegree (P.embeddings P.distinguished)
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree m)
          (P.embeddings P.distinguished) v) := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
  let := Family.PELCoordinates.familyPeriodScalarTower A ρ x
  apply (Family.ComplexCoordinates.familyComplexCoordinates A ρ x s hs hg hdegree).injective
  rw [Family.EmbeddingInclusion.familyEmbeddingInclusion_coordinates]
  funext τ
  rw [FieldMarkingComplexCoordinates.fieldMarking_complexCoordinates, Reference.FirstStandardCoordinates.referenceFirst_standardCoordinates]
  by_cases hτ : τ = P.embeddings P.distinguished
  · subst τ
    rw [Pi.single_eq_same, Pi.single_eq_same, AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso_apply]
  · rw [Pi.single_eq_of_ne hτ, Matrix.mulVec_zero, Pi.single_eq_of_ne hτ]

end

/-! The original embedding Lie rank determines the kernel dimension
of the reference first block under any actual full field marking. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s)
    (m : let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety)
    (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

def fieldMarkingFirstProjection : Geometry.ComplexBall.PrescribedSignsB.Vec →ₗ[ℂ] AlgebraicAction.AbelianModel (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
  let := Family.PELCoordinates.familyPeriodScalarTower A ρ x
  exact (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety).comp
    ((m.restrictScalars ℚ).toLinearMap.baseChange ℂ |>.comp (Reference.FirstEmbedding.referenceFirstComplexInclusion P hP))

theorem fieldMarkingFirstProjection_kernel :
    (fieldMarkingFirstProjection A ρ x s m P hP).ker =
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart (A.pullback x.left) (ρ.pullback x.left) s hs hg hdegree
        (P.embeddings P.distinguished)).comap
          (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree m)
            (P.embeddings P.distinguished)).toLinearMap := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
  let := Family.PELCoordinates.familyPeriodScalarTower A ρ x
  apply Submodule.ext
  intro v
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety
    ((m.restrictScalars ℚ).toLinearMap.baseChange ℂ (Reference.FirstEmbedding.referenceFirstComplexInclusion P hP v)) = 0 ↔ _
  rw [fieldMarking_referenceFirst, Family.EmbeddingInclusion.familyEmbeddingInclusion_kernel]
  rfl

include hs hg hdegree in
theorem fieldMarkingFirstProjection_finrank {r : ℕ}
    (hr : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.abelian.pullback x.left) (ρ.pullback x.left)
      ((P.embeddings P.distinguished).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r) :
    Module.finrank ℂ (fieldMarkingFirstProjection A ρ x s m P hP).ker = 3 - r := by
  rw [fieldMarkingFirstProjection_kernel, Submodule.comap_equiv_eq_map_symm]
  exact (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree m)
    (P.embeddings P.distinguished)).symm.finrank_map_eq _ |>.trans
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart_finrank (A.pullback x.left) (ρ.pullback x.left) s hs hg hdegree
        (P.embeddings P.distinguished) hr)

end

end OAI.RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank
