import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.RationalFractions
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.FiniteProjective

/-! # Local Coordinates -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.LocalCoordinates

noncomputable section

/-! The stalk coordinates of the constructed finite projection
are the normalized values of its defining homogeneous linear forms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.RationalFractions OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ChartFractions

theorem fraction_forms (n : ℕ) (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (a b s t : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (ha : a = b) (hs : s = t)
    (h1 : s.val ∉ x.asHomogeneousIdeal) (h2 : t.val ∉ x.asHomogeneousIdeal) :
    Projective.PointJets.StalkFractions.fraction n x a s h1 =
      Projective.PointJets.StalkFractions.fraction n x b t h2 := by
  subst b
  subst t
  rfl

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
  (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)
  (x : X.carrier) (i : Fin (m + 1)) (hi : (L i).val ∉ (X.embedding x).asHomogeneousIdeal)

theorem image_coordinate (a : Fin (m + 1)) :
    ChartFractions.image (FiniteProjective.FromForms.coordinates X m L) (RationalFractions.variableForm a) = L a := by
  apply Subtype.ext
  exact FiniteProjective.FromForms.coordinate X m L a

include hi in
theorem target_mem : MvPolynomial.X i ∉ (FiniteProjective.FromForms.map X m L h x).asHomogeneousIdeal := by
  apply RationalFractions.Restricted.target_mem (FiniteProjective.FromForms.coordinates X m L)
    X.embedding (FiniteProjective.FromForms.in_domain X m L h) i x
  rwa [FiniteProjective.FromForms.coordinate]

def targetCoordinate (a : Fin (m + 1)) :
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace m).presheaf.stalk (FiniteProjective.FromForms.map X m L h x) :=
  Projective.PointJets.StalkFractions.fraction m (FiniteProjective.FromForms.map X m L h x)
    (RationalFractions.variableForm a) (RationalFractions.variableForm i) (target_mem X m L h x i hi)

theorem pull (a : Fin (m + 1)) :
    (FiniteProjective.FromForms.map X m L h).stalkMap x (targetCoordinate X m L h x i hi a) =
      X.embedding.stalkMap x (Projective.PointJets.StalkFractions.fraction X.ambientDimension (X.embedding x) (L a) (L i) hi) := by
  have hs : FiniteProjective.FromForms.coordinates X m L (MvPolynomial.X i) ∉
      (X.embedding x).asHomogeneousIdeal := by rwa [FiniteProjective.FromForms.coordinate]
  have hp := RationalFractions.Restricted.pull (FiniteProjective.FromForms.coordinates X m L)
    X.embedding (FiniteProjective.FromForms.in_domain X m L h) i (RationalFractions.variableForm a) x hs
  exact hp.trans (congrArg (X.embedding.stalkMap x)
    (fraction_forms X.ambientDimension (X.embedding x) _ (L a) _ (L i)
      (image_coordinate X m L a) (image_coordinate X m L i) hs hi))

def sourceValue (c : Fin (X.ambientDimension + 1))
    (hc : X.embedding x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen X.ambientDimension c)
    (a : Fin (m + 1)) : X.carrier.presheaf.stalk x := by
  let := Stalk.PointAlgebra.scalarAlgebra (X.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension) x
  exact HomogeneousFormJets.form X.ambientDimension c
    (Projective.PointJets.coordinateGerm X.ambientDimension c X.embedding x hc) (L a)

theorem sourceValue_eq (c : Fin (X.ambientDimension + 1))
    (hc : X.embedding x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen X.ambientDimension c) (a : Fin (m + 1)) :
    sourceValue X m L x c hc a = X.embedding.stalkMap x
      (Projective.PointJets.StalkFractions.fraction X.ambientDimension (X.embedding x) (L a)
        (RationalFractions.variableForm c) hc) :=
  FormStalkComparison.form X.ambientDimension c X.embedding x hc (L a)

include hi in
theorem sourceValue_isUnit (c : Fin (X.ambientDimension + 1))
    (hc : X.embedding x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen X.ambientDimension c) :
    IsUnit (sourceValue X m L x c hc i) := by
  rw [sourceValue_eq]
  exact (Projective.PointJets.StalkFractions.isUnit X.ambientDimension (X.embedding x) (L i) (RationalFractions.variableForm c) hi hc).map
    (X.embedding.stalkMap x).hom

theorem normalized (c : Fin (X.ambientDimension + 1))
    (hc : X.embedding x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen X.ambientDimension c) (a : Fin (m + 1)) :
    sourceValue X m L x c hc i *
      (FiniteProjective.FromForms.map X m L h).stalkMap x (targetCoordinate X m L h x i hi a) =
        sourceValue X m L x c hc a := by
  rw [pull, sourceValue_eq, sourceValue_eq, ← map_mul, mul_comm]
  exact congrArg (X.embedding.stalkMap x)
    (Projective.PointJets.StalkFractions.mul X.ambientDimension (X.embedding x) (L a) (L i) (RationalFractions.variableForm c) hi hc)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.LocalCoordinates
