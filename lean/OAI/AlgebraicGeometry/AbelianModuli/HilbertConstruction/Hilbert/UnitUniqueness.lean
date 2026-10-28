import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FamilyGroupUniqueness

/-! # Unit Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.UnitUniqueness

noncomputable section

/-! The fixed Hilbert point and its actual embedded unit determine the
native abelian datum over a locally Noetherian test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u

private theorem doubleSubtype_ext {α : Type*} {p : α → Prop} {q : {a : α // p a} → Prop}
    {D E : {a : {b : α // p b} // q a}} (h : D.val.val = E.val.val) : D = E :=
  Subtype.ext (Subtype.ext h)

private theorem groupOperations_eq_of_embeddedUnit
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g : ℕ} {X : Over S}
    [SmoothOfRelativeDimension g X.hom] [GeometricallyConnected X.hom]
    (Q : Projective.ProjectivePresentations.ProjectivePresentation X) (D E : FamilyGroup.Operations.FamilyGroupOperations X) (hD : D.Laws) (hE : E.Laws)
    (hu : D.unit.left ≫ Q.embedding.left = E.unit.left ≫ Q.embedding.left) : D = E := by
  let : Mono Q.embedding := Over.mono_of_mono_left Q.embedding
  exact FamilyGroup.Operations.FamilyGroupOperations.eq_of_unit_eq_projective (g := g) Q D E hD hE
    ((cancel_mono Q.embedding).mp (Over.OverMorphism.ext hu))

private theorem boundedOperations_ext
    {B : Scheme.{u}} {A : Over B} [IsProper A.hom] [Smooth A.hom]
    {nm ni : ℕ} (jm : (A ⊗ A) ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver B nm)
    (ji : A ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver B ni)
    [IsClosedImmersion jm.left] [IsClosedImmersion ji.left]
    (Pm Pi : Polynomial ℚ) (T : Over B)
    (D E : Bounded.FamilyGroupPointClassification.BoundedCommutativeFamilyGroupOperations jm ji Pm Pi T)
    (h : D.val.val = E.val.val) : D = E :=
  doubleSubtype_ext h

private theorem boundedOperations_eq_of_embeddedUnit
    {B : Scheme.{u}} {A : Over B} [IsProper A.hom] [Smooth A.hom]
    {nm ni : ℕ} (jm : (A ⊗ A) ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver B nm)
    (ji : A ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver B ni)
    [IsClosedImmersion jm.left] [IsClosedImmersion ji.left]
    (Pm Pi : Polynomial ℚ) (T : Over B) [IsLocallyNoetherian T.left] {g : ℕ}
    [SmoothOfRelativeDimension g ((Over.pullback T.hom).obj A).hom]
    [GeometricallyConnected ((Over.pullback T.hom).obj A).hom]
    (Q : Projective.ProjectivePresentations.ProjectivePresentation ((Over.pullback T.hom).obj A))
    (D E : Bounded.FamilyGroupPointClassification.BoundedCommutativeFamilyGroupOperations jm ji Pm Pi T)
    (h : D.val.val.unit.left ≫ Q.embedding.left = E.val.val.unit.left ≫ Q.embedding.left) : D = E :=
  boundedOperations_ext jm ji Pm Pi T D E
    (groupOperations_eq_of_embeddedUnit (g := g) Q D.val.val E.val.val D.property E.property h)

private theorem subtype_sigma_eq_of_marks
    {I : Type*} {F : I → Type*} {p : (Σ i, F i) → Prop} {M : Type*}
    (mark : {z : Σ i, F i // p z} → M)
    (hf : ∀ (i : I) (d e : F i) (hd : p ⟨i, d⟩) (he : p ⟨i, e⟩),
      mark ⟨⟨i, d⟩, hd⟩ = mark ⟨⟨i, e⟩, he⟩ → d = e)
    (D E : {z : Σ i, F i // p z}) (hc : D.val.1 = E.val.1) (hm : mark D = mark E) : D = E := by
  rcases D with ⟨⟨i, d⟩, hd⟩
  rcases E with ⟨⟨j, e⟩, he⟩
  cases hc
  have hde := hf i d e hd he hm
  cases hde
  rfl

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ)
    (g : ℕ) (Pm Pi : Polynomial ℚ)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointData.FixedDimensionHilbertAbelianData.embeddedUnit {T : Over S}
    (D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T) :
    Over.mk (𝟙 T.left) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left n :=
  D.val.2.val.val.unit ≫ (D.val.projective S n P g Pm Pi).embedding

omit [AlgebraicGeometry.IsNoetherian S] in
private theorem nativeEmbeddedUnit_eq {T : Over S}
    (c : T ⟶ FixedDimension.Parameters.fixedDimensionHilbertParameter S n P g)
    (D : Bounded.FamilyGroupPointClassification.BoundedCommutativeFamilyGroupOperations
      (FixedDimension.GroupParameters.fixedDimensionHilbertMultiplicationPresentation S n P g).embedding
      (FixedDimension.GroupParameters.fixedDimensionHilbertInversionPresentation S n P g).embedding Pm Pi (Over.mk c.left))
    (hD : GeometricallyConnected (FixedDimension.GroupPointData.FixedDimensionHilbertGroupData.family S n P g Pm Pi ⟨c, D⟩).hom) :
    (FixedDimension.PointData.FixedDimensionHilbertAbelianData.embeddedUnit S n P g Pm Pi ⟨⟨c, D⟩, hD⟩).left =
      D.val.val.unit.left ≫ ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).baseChange c.left).embedding.left := rfl

omit [AlgebraicGeometry.IsNoetherian S] in
private theorem nativeOperations_eq_of_unitMark {T : Over S} [IsLocallyNoetherian T.left]
    (c : T ⟶ FixedDimension.Parameters.fixedDimensionHilbertParameter S n P g)
    (D E : Bounded.FamilyGroupPointClassification.BoundedCommutativeFamilyGroupOperations
      (FixedDimension.GroupParameters.fixedDimensionHilbertMultiplicationPresentation S n P g).embedding
      (FixedDimension.GroupParameters.fixedDimensionHilbertInversionPresentation S n P g).embedding Pm Pi (Over.mk c.left))
    (hD : GeometricallyConnected (FixedDimension.GroupPointData.FixedDimensionHilbertGroupData.family S n P g Pm Pi ⟨c, D⟩).hom)
    (hE : GeometricallyConnected (FixedDimension.GroupPointData.FixedDimensionHilbertGroupData.family S n P g Pm Pi ⟨c, E⟩).hom)
    (hu : FixedDimension.PointData.FixedDimensionHilbertAbelianData.embeddedUnit S n P g Pm Pi ⟨⟨c, D⟩, hD⟩ =
      FixedDimension.PointData.FixedDimensionHilbertAbelianData.embeddedUnit S n P g Pm Pi ⟨⟨c, E⟩, hE⟩) : D = E := by
  let V : Over (FixedDimension.Parameters.fixedDimensionHilbertParameter S n P g).left := Over.mk c.left
  let X : Over V.left := (Over.pullback V.hom).obj (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme
  let : IsLocallyNoetherian V.left := inferInstanceAs (IsLocallyNoetherian T.left)
  let : SmoothOfRelativeDimension g X.hom :=
    FixedDimension.GroupPointData.FixedDimensionHilbertGroupData.dimension S n P g Pm Pi ⟨c, D⟩
  let : GeometricallyConnected X.hom := hD
  exact boundedOperations_eq_of_embeddedUnit _ _ Pm Pi V (g := g)
    ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).baseChange c.left) D E
    ((nativeEmbeddedUnit_eq S n P g Pm Pi c D hD).symm.trans
      ((congrArg Over.Hom.left hu).trans (nativeEmbeddedUnit_eq S n P g Pm Pi c E hE)))

omit [AlgebraicGeometry.IsNoetherian S] in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointData.FixedDimensionHilbertAbelianData.eq_of_hilbert_eq_embeddedUnit
    {T : Over S} [IsLocallyNoetherian T.left]
    (D E : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T)
    (hc : D.val.1 = E.val.1)
    (hu : D.embeddedUnit S n P g Pm Pi = E.embeddedUnit S n P g Pm Pi) : D = E :=
  subtype_sigma_eq_of_marks (FixedDimension.PointData.FixedDimensionHilbertAbelianData.embeddedUnit S n P g Pm Pi)
    (nativeOperations_eq_of_unitMark S n P g Pm Pi) D E hc hu

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.UnitUniqueness
