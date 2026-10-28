import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.Enumeration
import OAI.AlgebraicGeometry.PELModuli.CMPoints.FiniteGroupPresentation
import OAI.AlgebraicGeometry.PELModuli.CMPoints.EtaleRank

/-! # Point Rank -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.PointRank

noncomputable section

/-! Geometric point cardinality of an actual finite etale fiber is
the rank of the original finite flat group. On a connected integral
base this rank agrees with its special-fiber rank. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.Enumeration.Lifts

theorem finiteEtaleGroup_card_eq_rank {k : Type} [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) [GrpObj X] [IsCommMonObj X]
    [IsFinite X.hom] [Etale X.hom] :
    Nat.card (Over.mk (𝟙 (Spec (.of k))) ⟶ X) = X.hom.finrank (IsLocalRing.closedPoint k) := by
  obtain ⟨H, e, _⟩ := PELModuli.CMPoints.FiniteGroupPresentation.finite_group_affine_presentation (CommGrp.mk X)
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : Etale H.scheme.hom := by
    rw [← e.hom.w]
    infer_instance
  calc
    Nat.card (Over.mk (𝟙 (Spec (.of k))) ⟶ X) =
        Nat.card (Over.mk (𝟙 (Spec (.of k))) ⟶ H.scheme) :=
      Nat.card_congr e.symm.homToEquiv
    _ = Module.finrank k H.algebra := (PELModuli.CMPoints.EtaleRank.finite_etale_group_basePoints_rank H).symm
    _ = H.scheme.hom.finrank (IsLocalRing.closedPoint k) :=
      (PELModuli.CMPoints.RankSpecialization.finite_group_geometric_rank H _).symm
    _ = X.hom.finrank (IsLocalRing.closedPoint k) := by
      rw [← e.hom.w]
      exact congrFun (Scheme.Hom.finrank_comp_left_of_isIso e.hom.left X.hom) _

theorem geometricPoints_card_eq_rank {S : Scheme}
    (X : Over S) [GrpObj X] [IsCommMonObj X] [IsFinite X.hom] [Flat X.hom]
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
    [Etale ((Over.pullback b).obj X).hom] :
    Nat.card (Over.mk b ⟶ X) = X.hom.finrank (b (IsLocalRing.closedPoint k)) := by
  let : GrpObj ((Over.pullback b).obj X) := Functor.grpObjObj (F := Over.pullback b)
  let : IsCommMonObj ((Over.pullback b).obj X) := Functor.isCommMonObj_obj (F := Over.pullback b) (M := X)
  have : IsFinite ((Over.pullback b).obj X).hom :=
    inferInstanceAs (IsFinite (Limits.pullback.snd X.hom b))
  calc
    Nat.card (Over.mk b ⟶ X) =
        Nat.card (Over.mk (𝟙 (Spec (.of k))) ⟶ (Over.pullback b).obj X) :=
      Nat.card_congr (Parameter.Enumeration.Lifts.parameterPullbackPointEquiv b X).symm
    _ = ((Over.pullback b).obj X).hom.finrank (IsLocalRing.closedPoint k) :=
      finiteEtaleGroup_card_eq_rank _
    _ = X.hom.finrank (b (IsLocalRing.closedPoint k)) :=
      Scheme.Hom.finrank_pullback_snd X.hom b _

theorem geometricPoints_card_eq_special_rank {S : Scheme} [PreconnectedSpace S]
    (X : Over S) [GrpObj X] [IsCommMonObj X] [IsFinite X.hom] [Flat X.hom]
    [LocallyOfFinitePresentation X.hom]
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
    [Etale ((Over.pullback b).obj X).hom] (s : S) :
    Nat.card (Over.mk b ⟶ X) = X.hom.finrank s :=
  (geometricPoints_card_eq_rank X b).trans
    (X.hom.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.PointRank
