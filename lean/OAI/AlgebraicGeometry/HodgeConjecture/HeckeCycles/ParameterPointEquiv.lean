import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation

/-! # Parameter Point Equiv -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointEquiv.CM

noncomputable section

/-! Passing a point to its actual parameter base is a group isomorphism,
and actual group endomorphisms commute with this passage. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo.CM.Naturality

local instance parameterEquivMonoidal {X Y : Scheme} (f : X ⟶ Y) : (Over.pullback f).Monoidal :=
  Over.instBraidedPullback.toMonoidal

variable {S : Scheme} (G : Grp (Over S)) {P T : Over S} (t : T ⟶ P)

local instance : GrpObj G.X := G.grp
local instance : GrpObj ((Over.pullback P.hom).obj G.X) :=
  ((Over.pullback P.hom).mapGrp.obj G).grp

def pointEquiv : (T ⟶ G.X) ≃* (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t ⟶ ((Over.pullback P.hom).mapGrp.obj G).X) where
  toFun := AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G t
  invFun x := (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).inv ≫ (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm x
  left_inv x := by
    change (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).inv ≫
      (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm
        (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t) ((AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).hom ≫ x)) = x
    rw [MulEquiv.symm_apply_apply]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ x) (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).inv_hom_id).trans (Category.id_comp x))
  right_inv x := by
    apply (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm.injective
    change (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm
      (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)
        ((AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).hom ≫ ((AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).inv ≫
          (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm x))) = _
    rw [MulEquiv.symm_apply_apply]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm x)
        (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).hom_inv_id).trans (Category.id_comp _))
  map_mul' := (ParameterPointTo.CM.Naturality.parameterizeMul G t).map_mul

theorem parameterize_map (a : T ⟶ G.X) (p : G.X ⟶ G.X) :
    AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G t (a ≫ p) = AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G t a ≫ (Over.pullback P.hom).map p := by
  apply (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm.injective
  have hright := BaseChangeEvaluation.CM.pointsEquiv_map P.hom (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t) p
    (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G t a)
  exact ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm_apply_apply _).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ p) ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm_apply_apply _).symm).trans
        hright.symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointEquiv.CM
