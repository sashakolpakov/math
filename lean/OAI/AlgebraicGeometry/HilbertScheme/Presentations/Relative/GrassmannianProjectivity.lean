import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.BaseChange

/-! # Grassmannian Projectivity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.GrassmannianProjectivity

noncomputable section

/-!
A closed projective embedding of the Grassmannian over an arbitrary scheme.
Relative projective space is the base change of polynomial Proj over the
base scheme's ring of global functions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

namespace PolynomialProjective

def relativeProjectiveSpace (σ : Type u) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (Projective.Flatness.GradedHilbert.projectiveStructureMap (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ Γ(S, ⊤))) S.toSpecΓ

def relativeProjectiveSpaceProjection (σ : Type u) (S : Scheme.{u}) :
    relativeProjectiveSpace σ S ⟶ S := pullback.snd _ _

def relativeProjectiveSpaceCoefficientMap (σ : Type u) (S : Scheme.{u}) :
    relativeProjectiveSpace σ S ⟶ Proj (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ Γ(S, ⊤)) := pullback.fst _ _

theorem relativeProjectiveSpace_isPullback (σ : Type u) (S : Scheme.{u}) :
    IsPullback (relativeProjectiveSpaceCoefficientMap σ S) (relativeProjectiveSpaceProjection σ S)
      (Projective.Flatness.GradedHilbert.projectiveStructureMap (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ Γ(S, ⊤))) S.toSpecΓ :=
  IsPullback.of_hasPullback _ _

end PolynomialProjective

namespace Grassmannian

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable (S : Scheme.{u})

def relativeGrassmannianPluckerEmbedding : Grassmannian.Gluing.grassmannianScheme (ι := ι) (ν := ν) S ⟶
    PolynomialProjective.relativeProjectiveSpace (ι → ν) S :=
  pullback.lift
    (Grassmannian.BaseMap.grassmannianBaseMap S.toSpecΓ ≫ Grassmannian.Projectivity.grassmannianPluckerEmbedding Γ(S, ⊤))
    (Grassmannian.Gluing.grassmannianStructureMap S) (by
      rw [Category.assoc, Grassmannian.Projectivity.grassmannianPluckerEmbedding_over]
      exact Grassmannian.BaseMap.grassmannianBaseMap_over S.toSpecΓ)

theorem relativeGrassmannianPluckerEmbedding_coefficient :
    relativeGrassmannianPluckerEmbedding (ι := ι) (ν := ν) S ≫
        PolynomialProjective.relativeProjectiveSpaceCoefficientMap (ι → ν) S =
      Grassmannian.BaseMap.grassmannianBaseMap S.toSpecΓ ≫ Grassmannian.Projectivity.grassmannianPluckerEmbedding Γ(S, ⊤) :=
  pullback.lift_fst _ _ _

theorem relativeGrassmannianPluckerEmbedding_over :
    relativeGrassmannianPluckerEmbedding (ι := ι) (ν := ν) S ≫
      PolynomialProjective.relativeProjectiveSpaceProjection (ι → ν) S = Grassmannian.Gluing.grassmannianStructureMap S :=
  pullback.lift_snd _ _ _

theorem relativeGrassmannianPluckerEmbedding_isPullback :
    IsPullback (Grassmannian.BaseMap.grassmannianBaseMap S.toSpecΓ) (relativeGrassmannianPluckerEmbedding (ι := ι) (ν := ν) S)
      (Grassmannian.Projectivity.grassmannianPluckerEmbedding Γ(S, ⊤)) (PolynomialProjective.relativeProjectiveSpaceCoefficientMap (ι → ν) S) := by
  have h : IsPullback (Grassmannian.BaseMap.grassmannianBaseMap S.toSpecΓ)
      (relativeGrassmannianPluckerEmbedding (ι := ι) (ν := ν) S ≫
        PolynomialProjective.relativeProjectiveSpaceProjection (ι → ν) S)
      (Grassmannian.Projectivity.grassmannianPluckerEmbedding (ι := ι) (ν := ν) Γ(S, ⊤) ≫
        Projective.Flatness.GradedHilbert.projectiveStructureMap (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (ι → ν) Γ(S, ⊤))) S.toSpecΓ := by
    rw [relativeGrassmannianPluckerEmbedding_over, Grassmannian.Projectivity.grassmannianPluckerEmbedding_over]
    exact Grassmannian.BaseChange.grassmannianBaseMap_isPullback S.toSpecΓ
  exact h.of_bot (relativeGrassmannianPluckerEmbedding_coefficient S).symm
    (PolynomialProjective.relativeProjectiveSpace_isPullback (ι → ν) S)

instance relativeGrassmannianPluckerEmbedding_isClosedImmersion :
    IsClosedImmersion (relativeGrassmannianPluckerEmbedding (ι := ι) (ν := ν) S) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (relativeGrassmannianPluckerEmbedding_isPullback S)
    (Grassmannian.Projectivity.grassmannianPluckerEmbedding_isClosedImmersion Γ(S, ⊤))

/-- The constructed Grassmannian admits a closed embedding over its base into
finite-dimensional relative projective space. -/
theorem grassmannian_projective_embedding [Finite ν] :
    ∃ e : Grassmannian.Gluing.grassmannianScheme (ι := ι) (ν := ν) S ⟶ PolynomialProjective.relativeProjectiveSpace (ι → ν) S,
      IsClosedImmersion e ∧ e ≫ PolynomialProjective.relativeProjectiveSpaceProjection (ι → ν) S =
        Grassmannian.Gluing.grassmannianStructureMap (ι := ι) (ν := ν) S :=
  ⟨relativeGrassmannianPluckerEmbedding S, inferInstance, relativeGrassmannianPluckerEmbedding_over S⟩

end Grassmannian

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.GrassmannianProjectivity
