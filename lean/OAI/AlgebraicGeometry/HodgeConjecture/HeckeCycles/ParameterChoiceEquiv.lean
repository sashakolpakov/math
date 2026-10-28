import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterSubgroupProperties
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterModelDescent

/-! # Parameter Choice Equiv -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterChoiceEquiv.CM

noncomputable section

/-! The actual native subgroup parameters commute with passing to their
test-scheme base. Finite locally free models, elementary group types,
torsion bounds, and the original projector support are all retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo.CM.RelativeSubgroup OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterSubgroupProperties.CM

local instance parameterChoicePullbackMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Over.pullback f).Monoidal := Over.instBraidedPullback.toMonoidal

variable {S : Scheme} (G : Grp (Over S)) (P : Over S)
  (n : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]

local instance : GrpObj G.X := G.grp
local instance : GrpObj ((Over.pullback P.hom).obj G.X) :=
  ((Over.pullback P.hom).mapGrp.obj G).grp

def toChoice (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice G.X n M P) :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice ((Over.pullback P.hom).mapGrp.obj G).X n M (Over.mk (𝟙 P.left)) where
  subgroup := AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F.subgroup
  killed := AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter_killed G P F.subgroup n F.killed
  moduleType := ParameterSubgroupProperties.CM.toParameter_type G P F.subgroup M F.moduleType
  geometric := F.geometric.map (AbelianScheme.IsogenyQuotient.Parameter.SubgroupModel.Construction.relativeSubgroupOverParameter_model G P F.subgroup)

def fromChoice
    (H : AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice ((Over.pullback P.hom).mapGrp.obj G).X n M (Over.mk (𝟙 P.left))) :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice G.X n M P where
  subgroup := ParameterPointTo.CM.RelativeSubgroup.fromParameter G P H.subgroup
  killed := ParameterSubgroupProperties.CM.fromParameter_killed G P H.subgroup n H.killed
  moduleType := ParameterSubgroupProperties.CM.fromParameter_type G P H.subgroup M H.moduleType
  geometric := H.geometric.map (ParameterModelDescent.CM.model G P H.subgroup)

def choiceEquiv : AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice G.X n M P ≃
    AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice ((Over.pullback P.hom).mapGrp.obj G).X n M (Over.mk (𝟙 P.left)) where
  toFun := toChoice G P n M
  invFun := fromChoice G P n M
  left_inv F := AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice.ext (ParameterPointTo.CM.RelativeSubgroup.from_to G P F.subgroup)
  right_inv H := AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice.ext (ParameterPointTo.CM.RelativeSubgroup.to_from G P H.subgroup)

def supportedEquiv (p : G.X ⟶ G.X) : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice G.X n M p P ≃
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice ((Over.pullback P.hom).mapGrp.obj G).X n M ((Over.pullback P.hom).map p)
      (Over.mk (𝟙 P.left)) where
  toFun F := ⟨choiceEquiv G P n M F.val, ParameterSubgroupProperties.CM.toParameter_supported G P F.val.subgroup p F.property⟩
  invFun H := ⟨(choiceEquiv G P n M).symm H.val, ParameterSubgroupProperties.CM.fromParameter_supported G P H.val.subgroup p H.property⟩
  left_inv F := Subtype.ext ((choiceEquiv G P n M).symm_apply_apply F.val)
  right_inv H := Subtype.ext ((choiceEquiv G P n M).apply_symm_apply H.val)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterChoiceEquiv.CM
