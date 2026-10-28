import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Product Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductRestriction

noncomputable section

section

/-! Restricting a product along an actual open and closed immersion
produces another smooth projective product presentation. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable {X X' Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (i : X'.toOver ⟶ X.toOver) [IsOpenImmersion i.left] [IsClosedImmersion i.left]

def raw : Over Foundations.Scheme.ProjectiveSpace.complexBase := pullback P.fst i

def inclusionRaw : raw P i ⟶ P.space.toOver := pullback.fst P.fst i

def firstRaw : raw P i ⟶ X'.toOver := pullback.snd P.fst i

def secondRaw : raw P i ⟶ Y.toOver := inclusionRaw P i ≫ P.snd

omit [IsOpenImmersion i.left] [IsClosedImmersion i.left] in
theorem isPullback : IsPullback (inclusionRaw P i).left (firstRaw P i).left P.fst.left i.left :=
  (IsPullback.of_hasPullback P.fst i).map (Over.forget Foundations.Scheme.ProjectiveSpace.complexBase)

instance inclusion_open : IsOpenImmersion (inclusionRaw P i).left :=
  MorphismProperty.of_isPullback (isPullback P i).flip (inferInstance : IsOpenImmersion i.left)

instance inclusion_closed : IsClosedImmersion (inclusionRaw P i).left :=
  MorphismProperty.of_isPullback (isPullback P i).flip (inferInstance : IsClosedImmersion i.left)

def space : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation where
  carrier := (raw P i).left
  structureMap := (raw P i).hom
  projective := {
    ambientDimension := P.space.ambientDimension
    embedding := (inclusionRaw P i).left ≫ P.space.embedding
    closedImmersion := by infer_instance
    over_base := by
      rw [Category.assoc, P.space.embedding_over]
      exact (inclusionRaw P i).w }
  smooth := by
    have hs : Smooth ((inclusionRaw P i).left ≫ P.space.structureMap) := inferInstance
    have hw : (inclusionRaw P i).left ≫ P.space.structureMap = (raw P i).hom := (inclusionRaw P i).w
    exact hw ▸ hs

def presentation : ProperCycleLinearity.ProductPresentation X' Y where
  space := ProductRestriction.space P i
  fst := firstRaw P i
  snd := secondRaw P i
  isLimit := BinaryFan.IsLimit.mk _
    (fun a b => pullback.lift (BinaryFan.IsLimit.lift P.isLimit (a ≫ i) b) a
      (BinaryFan.IsLimit.lift_fst P.isLimit (a ≫ i) b))
    (fun a b => pullback.lift_snd _ _ _)
    (fun a b => by
      change pullback.lift _ _ _ ≫ (pullback.fst P.fst i ≫ P.snd) = b
      rw [← Category.assoc, pullback.lift_fst]
      exact BinaryFan.IsLimit.lift_snd P.isLimit (a ≫ i) b)
    (fun a b u hu₁ hu₂ => by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        apply BinaryFan.IsLimit.hom_ext P.isLimit
        · change u ≫ pullback.fst P.fst i ≫ P.fst = _
          rw [pullback.condition, ← Category.assoc]
          exact (congrArg (fun z => z ≫ i) hu₁).trans
            (BinaryFan.IsLimit.lift_fst P.isLimit (a ≫ i) b).symm
        · exact hu₂.trans (BinaryFan.IsLimit.lift_snd P.isLimit (a ≫ i) b).symm
      · rw [pullback.lift_snd]
        exact hu₁)

def inclusion : (presentation P i).space.toOver ⟶ P.space.toOver := inclusionRaw P i

instance : IsOpenImmersion (inclusion P i).left := inclusion_open P i
instance : IsClosedImmersion (inclusion P i).left := inclusion_closed P i

theorem first : inclusion P i ≫ P.fst = (presentation P i).fst ≫ i := pullback.condition

theorem second : inclusion P i ≫ P.snd = (presentation P i).snd := rfl

theorem graph {f' : X'.toOver ⟶ Y.toOver} {f : X.toOver ⟶ Y.toOver} (hf : i ≫ f = f') :
    (presentation P i).graph f' ≫ inclusion P i = i ≫ P.graph f := by
  apply BinaryFan.IsLimit.hom_ext P.isLimit
  · change ((presentation P i).graph f' ≫ inclusion P i) ≫ P.fst = (i ≫ P.graph f) ≫ P.fst
    rw [Category.assoc, first P i, ← Category.assoc, ProperCycleLinearity.ProductPresentation.graph_fst, Category.id_comp,
      Category.assoc, ProperCycleLinearity.ProductPresentation.graph_fst, Category.comp_id]
  · change ((presentation P i).graph f' ≫ inclusion P i) ≫ P.snd = (i ≫ P.graph f) ≫ P.snd
    rw [Category.assoc, second P i, ProperCycleLinearity.ProductPresentation.graph_snd, Category.assoc, ProperCycleLinearity.ProductPresentation.graph_snd, hf]

end

/-! Restriction of the target factor of a product along an actual open
and closed immersion, with its canonical graph factorization. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace Target

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

def swap {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y) : ProperCycleLinearity.ProductPresentation Y X where
  space := P.space
  fst := P.snd
  snd := P.fst
  isLimit := BinaryFan.isLimitFlip P.isLimit

variable {X V Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (i : V.toOver ⟶ Y.toOver) [IsOpenImmersion i.left] [IsClosedImmersion i.left]

def presentation : ProperCycleLinearity.ProductPresentation X V := swap (ProductRestriction.presentation (swap P) i)

def inclusion : (presentation P i).space.toOver ⟶ P.space.toOver :=
  ProductRestriction.inclusion (swap P) i

instance : IsOpenImmersion (inclusion P i).left := inclusion_open (swap P) i
instance : IsClosedImmersion (inclusion P i).left := inclusion_closed (swap P) i

theorem first : inclusion P i ≫ P.fst = (presentation P i).fst := rfl

theorem second : inclusion P i ≫ P.snd = (presentation P i).snd ≫ i :=
  ProductRestriction.first (swap P) i

theorem graph {f' : X.toOver ⟶ V.toOver} {f : X.toOver ⟶ Y.toOver} (hf : f' ≫ i = f) :
    (presentation P i).graph f' ≫ inclusion P i = P.graph f := by
  apply BinaryFan.IsLimit.hom_ext P.isLimit
  · change ((presentation P i).graph f' ≫ inclusion P i) ≫ P.fst = P.graph f ≫ P.fst
    rw [Category.assoc, first P i, ProperCycleLinearity.ProductPresentation.graph_fst, ProperCycleLinearity.ProductPresentation.graph_fst]
  · change ((presentation P i).graph f' ≫ inclusion P i) ≫ P.snd = P.graph f ≫ P.snd
    rw [Category.assoc, second P i, ← Category.assoc, ProperCycleLinearity.ProductPresentation.graph_snd,
      ProperCycleLinearity.ProductPresentation.graph_snd, hf]

end Target

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductRestriction
