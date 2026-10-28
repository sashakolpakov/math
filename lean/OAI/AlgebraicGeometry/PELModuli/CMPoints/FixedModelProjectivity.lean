import OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedProjectiveEmbeddingDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Parameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupAmpleBundle
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Fixed Model Projectivity -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedModelProjectivity

noncomputable section

/-! A specified arithmetic abelian model becomes projective over a
finite extension. Its underlying family is the literal base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Parameter

theorem affine_projective_embedding_of_native
    {R : Type} [CommRing R] {X : Over (Spec (.of R))}
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) :
    ∃ i : X ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R P.dimension, IsClosedImmersion i.left := by
  have : IsClosedImmersion P.embedding.left := P.closedImmersion
  let e := AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) P.dimension
  have : IsIso e.hom.left := ((Over.forget (Spec (.of R))).mapIso e).isIso_hom
  exact ⟨P.embedding ≫ e.hom,
    inferInstanceAs (IsClosedImmersion (P.embedding.left ≫ e.hom.left))⟩

theorem e34_presentation_of_affine_embedding
    {R : Type} [CommRing R] {X : Over (Spec (.of R))} {n : ℕ}
    (j : X ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n) (hj : IsClosedImmersion j.left) :
    Nonempty (HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) := by
  let e := AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n
  have : IsClosedImmersion j.left := hj
  have : IsIso e.inv.left := ((Over.forget (Spec (.of R))).mapIso e).isIso_inv
  let B : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X := {
    dimension := n
    embedding := j ≫ e.inv
    closedImmersion := inferInstanceAs (IsClosedImmersion (j.left ≫ e.inv.left)) }
  exact ⟨IntegralModel.Presentations.Parameter.e34ProjectivePresentationOfNative B⟩

theorem fixed_coefficient_embedding_gives_arithmetic_projectivity
    {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] (κ : K →+* ℂ)
    (ιL : L →+* ℂ) (hιL : ιL.comp (algebraMap K L) = κ)
    (X : Over (Spec (.of K))) (s : Finset L) (n : ℕ)
    (j : (Over.pullback (IntegralModel.Fixed.CoefficientModels.Coefficients.parameterBaseMap K L s)).obj X ⟶
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s) n)
    (hj : IsClosedImmersion j.left) :
    ∃ F : IntegralModel.Base.ArithmeticBaseExtension K κ,
      Nonempty (HilbertScheme.Presentations.Has.Core.ProjectivePresentation ((Over.pullback F.fieldExtension).obj X)) := by
  let := CoefficientFields.algebraicCoefficientField K L s
  let := CoefficientFields.algebraicCoefficientNumberField K L s
  have : Module.Finite K (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s) := CoefficientFields.algebraicCoefficientRing_finite K L s
  let F : IntegralModel.Base.ArithmeticBaseExtension K κ := {
    extension := ⟨ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s⟩
    embedding := ιL.comp (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s).val.toRingHom
    embedding_extends := by
      ext a
      exact RingHom.congr_fun hιL a
    denominator := 1
    denominator_ne_zero := one_ne_zero }
  exact ⟨F, e34_presentation_of_affine_embedding j hj⟩

theorem fixed_abelian_model_projective_after_finite_extension
    {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K))) :
    ∃ F : IntegralModel.Base.ArithmeticBaseExtension K κ,
      Nonempty (HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.pullback F.fieldExtension).scheme) := by
  let L := AlgebraicClosure K
  let AL := A.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  obtain ⟨P⟩ := ArithmeticGeometry.OrdinaryLocus.Openness.GroupAmpleBundle.Construction.group_projectivePresentation AL.scheme
  obtain ⟨i, hi⟩ := affine_projective_embedding_of_native P
  obtain ⟨s, j, hj⟩ := @FixedProjectiveEmbeddingDescent.fixed_projective_embedding_descends K L _ _ _ _ A.scheme
    ⟨inferInstance, inferInstance, inferInstance⟩ P.dimension i hi
  let : Algebra K ℂ := κ.toAlgebra
  let embeddingL : L →ₐ[K] ℂ := IsAlgClosed.lift
  exact fixed_coefficient_embedding_gives_arithmetic_projectivity κ embeddingL.toRingHom
    (by ext a; exact embeddingL.commutes a) A.scheme s P.dimension j hj

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedModelProjectivity
