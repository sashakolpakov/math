import OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianField
import OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projectivity

/-! # Special Fiber Projectivity -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Projectivity of the actual special fiber follows from its abelian-scheme structure over the finite field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange

theorem SpecialFiberProjectivity.projectivePresentation_projectiveOver {K : Type} [Field K]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of K)) (P : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f)) :
    IntegralComparison.Projectivity.Construction.ProjectiveOver K f := by
  obtain ⟨e⟩ : Nonempty (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) P.dimension ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K P.dimension) := ⟨AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of K) P.dimension⟩
  let i : Over.mk f ⟶ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K P.dimension := P.embedding ≫ e.hom
  let : IsIso e.hom.left := ((Over.forget (Spec (.of K))).mapIso e).isIso_hom
  have hi : IsClosedImmersion i.left :=
    inferInstanceAs (IsClosedImmersion (P.embedding.left ≫ e.hom.left))
  refine ⟨P.dimension, i.left, hi, ?_⟩
  change i.left ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K P.dimension).hom = f
  exact i.w

theorem SpecialFiberProjectivity.abelianScheme_projectiveOver {K : Type} [Field K] {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K))) : IntegralComparison.Projectivity.Construction.ProjectiveOver K A.scheme.hom := by
  obtain ⟨L, hL⟩ := AbelianField.AbelianFieldAmple.exists_ample A
  exact SpecialFiberProjectivity.projectivePresentation_projectiveOver A.scheme.hom (hL.projectivePresentation A.scheme.hom)

theorem Geometry.AbelianH1Model.specialFiber_projective {K : Type} [Field K] [NumberField K]
    {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq) :
    IntegralComparison.Projectivity.Construction.ProjectiveOver (ZMod q) A.specialFiber.scheme.hom :=
  SpecialFiberProjectivity.abelianScheme_projectiveOver A.specialFiber

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
