import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ConditionIdeals
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.IdealBaseChange

/-! # Ideal Chart Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.IdealChartPullback

noncomputable section

/-! A closed chart whose defining ideal is the pulled-back ideal gives an actual Cartesian family square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {P Q Z : Scheme.{u}} (I : P.IdealSheafData)
variable (j : Z ⟶ Q) (p : Q ⟶ P) (hI : I.comap p = j.ker)

include hI in
theorem closedIdealChart_le_kernel : I ≤ (j ≫ p).ker := by
  apply (ConditionIdeals.ideal_comap_eq_bot_iff I (j ≫ p)).mp
  rw [I.comap_comp, hI]
  exact (ConditionIdeals.ideal_comap_eq_bot_iff j.ker j).mpr le_rfl

def closedIdealChartMap : Z ⟶ I.subscheme :=
  IsClosedImmersion.lift I.subschemeι (j ≫ p)
    (I.ker_subschemeι.symm ▸ closedIdealChart_le_kernel I j p hI)

theorem closedIdealChartMap_embedding :
    closedIdealChartMap I j p hI ≫ I.subschemeι = j ≫ p :=
  IsClosedImmersion.lift_fac _ _ _

variable [IsClosedImmersion j]

theorem closedIdealChartMap_isPullback :
    IsPullback (closedIdealChartMap I j p hI) j I.subschemeι p := by
  apply (isPullback_of_isClosedImmersion j I.subschemeι
    (closedIdealChartMap I j p hI) p (closedIdealChartMap_embedding I j p hI).symm ?_).flip
  exact (congrArg (fun J => J.comap p) I.ker_subschemeι).trans hI

theorem closedIdealChartFamily_isPullback {S T : Scheme.{u}} (q : Q ⟶ T)
    (f : P ⟶ S) (x : T ⟶ S) (h : IsPullback p q f x) :
    IsPullback (closedIdealChartMap I j p hI) (j ≫ q) (I.subschemeι ≫ f) x :=
  (closedIdealChartMap_isPullback I j p hI).paste_vert h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.IdealChartPullback
