import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.PointJets
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.PointDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IndependentLinearCut

/-! # Point Jet Coordinates -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointJetCoordinates

noncomputable section

/-! First-order coordinates at finitely many actual points can be
made independent while retaining a center disjoint from the projective scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier) (hp : p ≫ X.structureMap = 𝟙 _)

def coordinate : Fin (X.ambientDimension + 1) :=
  Classical.choose (Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen X.ambientDimension
    (X.embedding (p (IsLocalRing.closedPoint ℂ))))

theorem coordinate_mem :
    X.embedding (p (IsLocalRing.closedPoint ℂ)) ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen X.ambientDimension (coordinate X p) :=
  Classical.choose_spec (Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen X.ambientDimension
    (X.embedding (p (IsLocalRing.closedPoint ℂ))))

include hp in
theorem over : p ≫ (X.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension) = 𝟙 _ := by
  rw [X.embedding_over, hp]

abbrev space :=
  letI := Stalk.PointAlgebra.scalarAlgebra (X.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension)
    (p (IsLocalRing.closedPoint ℂ))
  ℂ × (AugmentedCotangent.ideal (Stalk.PointAlgebra.evaluation
    (X.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension) p (over X p hp))).Cotangent

abbrev scalar := Stalk.PointAlgebra.scalarAlgebra
  (X.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension) (p (IsLocalRing.closedPoint ℂ))

attribute [local instance] scalar

def map : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 →ₗ[ℂ] space X p hp :=
  Projective.PointJets.map X.ambientDimension (coordinate X p) X.embedding p
    (over X p hp) (coordinate_mem X p)

theorem surjective : Function.Surjective (map X p hp) :=
  Projective.PointJets.surjective X.ambientDimension (coordinate X p) X.embedding p
    (over X p hp) (coordinate_mem X p)

variable (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]

include m in
theorem finite : Module.Finite ℂ (space X p hp) := by
  let : SmoothOfRelativeDimension m (X.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension) := by
    rw [X.embedding_over]
    infer_instance
  let := Stalk.PointAlgebra.finite_cotangent
    (X.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension) m p (over X p hp)
  infer_instance

theorem dimension : Module.finrank ℂ (space X p hp) = m + 1 := by
  let : SmoothOfRelativeDimension m (X.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension) := by
    rw [X.embedding_over]
    infer_instance
  apply Stalk.PointAlgebra.jet_dimension
    (X.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension) m p (over X p hp)
  apply Closed.PointDimension.coheight X m
  exact ((pointEquivClosedPoint X.structureMap) ⟨p, hp⟩).property

def equivalence : space X p hp ≃ₗ[ℂ] (Fin (m + 1) → ℂ) := by
  let := finite X p hp m
  exact LinearEquiv.ofFinrankEq _ _ (by rw [dimension X p hp m, Module.finrank_fin_fun])

theorem exists_forms {ι : Type} [Finite ι]
    (p : ι → (Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier)) (hp : ∀ j, p j ≫ X.structureMap = 𝟙 _) :
    ∃ L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      (∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal) ∧
      ∀ j, LinearIndependent ℂ (fun a => map X (p j) (hp j) (L a)) := by
  let D j := (equivalence X (p j) (hp j) m).toLinearMap.comp (map X (p j) (hp j))
  have hD : ∀ j, Function.Surjective (D j) := fun j =>
    (equivalence X (p j) (hp j) m).surjective.comp (PointJetCoordinates.surjective X (p j) (hp j))
  obtain ⟨L, hav, hLI⟩ := IndependentLinearCut.exists_full X m D hD
  refine ⟨L, hav, fun j => ?_⟩
  exact LinearIndependent.of_comp (equivalence X (p j) (hp j) m).toLinearMap (hLI j)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointJetCoordinates
