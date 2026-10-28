import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ImmersionFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GraphSupport

/-! # Factorization Base Change Ideal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.FactorizationBaseChangeIdeal

noncomputable section

/-! The ideal obstructing factorization through a closed immersion commutes with actual over-scheme base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} {X P Z : Over S}
variable (j : Z ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P) (c : T ⟶ S)

theorem closedFactorizationIdeal_baseChange :
    ((Over.pullback c).map j).left.ker.comap ((Over.pullback c).map i).left =
      (j.left.ker.comap i.left).comap (pullback.fst X.hom c) := by
  have hj := Graph.FamilyBaseChange.closedImmersion_ker_baseChange (Graph.FamilyBaseChange.overPullback_map_isPullback_flip c j)
  have hi : ((Over.pullback c).map i).left ≫ pullback.fst P.hom c = pullback.fst X.hom c ≫ i.left :=
    pullback.lift_fst _ _ _
  rw [hj]
  exact (j.left.ker.comap_comp _ _).symm.trans
    ((congrArg (fun a => j.left.ker.comap a) hi).trans (j.left.ker.comap_comp _ _))

theorem closedFactorization_baseChange_iff_ideal_zero :
    (j.left.ker.comap i.left).comap (pullback.fst X.hom c) = ⊥ ↔
      ∃! h : (Over.pullback c).obj X ⟶ (Over.pullback c).obj Z,
        h ≫ (Over.pullback c).map j = (Over.pullback c).map i := by
  have : IsClosedImmersion ((Over.pullback c).map j).left := Projective.PresentationBaseChange.overPullback_map_closed j c
  rw [← closedFactorizationIdeal_baseChange j i c]
  exact ImmersionFactorization.closedImmersion_ideal_factorization ((Over.pullback c).map j) ((Over.pullback c).map i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.FactorizationBaseChangeIdeal
