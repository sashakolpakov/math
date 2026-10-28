import OAI.ArithmeticGeometry.Descent.CMVariety.LevelComparison

/-! # Countable Levels -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableLevels

noncomputable section

/-! Full ordered levels on a fixed complex abelian scheme form a
finite set, by their actual locally constant label parameters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

theorem finite_full_levels {g N : ℕ} [NeZero N]
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (level : A.FullLevel N) :
    Finite (A.FullLevel N) := by
  let x : Foundations.Scheme.ProjectiveSpace.complexBase := Classical.arbitrary Foundations.Scheme.ProjectiveSpace.complexBase
  let label := fun l : A.FullLevel N => level.labelsEquiv l x
  apply Finite.of_injective label
  intro l m hlm
  apply level.labelsEquiv.injective
  exact ((level.labelsEquiv l).eq_const x).trans
    ((congrArg (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase) hlm).trans ((level.labelsEquiv m).eq_const x).symm)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableLevels
