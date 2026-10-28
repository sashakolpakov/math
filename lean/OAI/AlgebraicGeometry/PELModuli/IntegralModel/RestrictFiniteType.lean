import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypePullback
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteTypeIso

/-! # Restrict Finite Type -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.RestrictFiniteType

noncomputable section

/-! Finite type of a coherent module passes to its actual open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteTypeIso

universe u

theorem module_restrict_finiteType
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : X.Opens) : (M.restrict U.ι).IsFiniteType := by
  let : ((pullback U.ι).obj M).IsFiniteType := Finite.TypePullback.module_pullback_finiteType U.ι M
  exact SheafCohomology.Projective.FiniteTypeIso.finiteType_of_iso ((restrictFunctorIsoPullback U.ι).app M).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.RestrictFiniteType
