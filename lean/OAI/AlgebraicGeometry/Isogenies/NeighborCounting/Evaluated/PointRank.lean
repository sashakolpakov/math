import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitPointSurjectivity
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Sections
import OAI.RepresentationTheory.Theta.Geometric.ConstantSchemeDegree

/-! # Point Rank -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointRank.Lifts

noncomputable section

/-! The cardinality of evaluated generic points is the rank of the
actual finite flat source. This connects native block rank to the linear
dimension used in the exhaustive kernel enumeration. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (R L : Type) [CommRing R] [Field L] [Algebra R L]
variable (A : Over (Spec (.of R)))

local instance unit_preconnected : PreconnectedSpace (𝟙_ (Over (Spec (.of L)))).left :=
  inferInstanceAs (PreconnectedSpace (Spec (.of L)))

def genericPointPullbackEquiv :
    (Sections.Lifts.genericTest R L ⟶ A) ≃ ((𝟙_ (Over (Spec (.of L)))) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj A) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap R L))
  let e : (Over.map s).obj (𝟙_ (Over (Spec (.of L)))) ≅ Sections.Lifts.genericTest R L :=
    Over.isoMk (Iso.refl _) (by simp [Sections.Lifts.genericTest, s])
  exact e.homFromEquiv.symm.trans ((Over.mapPullbackAdj s).homEquiv _ A)

variable {I : Type}
variable (eA : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj A)

def evaluatedPointLabels : (Sections.Lifts.genericTest R L ⟶ A) ≃ I :=
  (genericPointPullbackEquiv R L A).trans (eA.symm.homToEquiv.trans
    ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of L)) I (𝟙_ (Over (Spec (.of L))))).trans {
      toFun c := c (IsLocalRing.closedPoint L)
      invFun i := LocallyConstant.const _ i
      left_inv c := (c.eq_const (IsLocalRing.closedPoint L)).symm
      right_inv _ := rfl }))

include eA in
theorem evaluatedPoint_card : Nat.card (Sections.Lifts.genericTest R L ⟶ A) = Nat.card I :=
  Nat.card_congr (evaluatedPointLabels R L A eA)

variable [Finite I] [IsFinite A.hom] [Flat A.hom]

include eA in
theorem evaluatedPoint_card_eq_rank :
    Nat.card (Sections.Lifts.genericTest R L ⟶ A) = A.hom.finrank
      (Spec.map (CommRingCat.ofHom (algebraMap R L)) (IsLocalRing.closedPoint L)) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap R L))
  have : IsIso eA.hom.left := (Over.forget _).map_isIso eA.hom
  have : Flat ((Over.pullback s).obj A).hom :=
    inferInstanceAs (Flat (Limits.pullback.snd A.hom s))
  have : IsFinite ((Over.pullback s).obj A).hom :=
    inferInstanceAs (IsFinite (Limits.pullback.snd A.hom s))
  have hc : (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I).hom.finrank =
      ((Over.pullback s).obj A).hom.finrank := by
    rw [← eA.hom.w]
    exact Scheme.Hom.finrank_comp_left_of_isIso eA.hom.left ((Over.pullback s).obj A).hom
  exact (evaluatedPoint_card R L A eA).trans
    ((RepresentationTheory.Theta.Geometric.ConstantSchemeDegree.constantScheme_finrank L I (IsLocalRing.closedPoint L)).symm.trans
      ((congrFun hc (IsLocalRing.closedPoint L)).trans
        (Scheme.Hom.finrank_pullback_snd A.hom s (IsLocalRing.closedPoint L))))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointRank.Lifts
