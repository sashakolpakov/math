import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointEquiv
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupFunctor

/-! # Parameter Subgroup Properties -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterSubgroupProperties.CM

noncomputable section

/-! The parameter-base equivalence preserves the exact torsion bound,
geometric elementary group type, and support on the actual projector. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo.CM.RelativeSubgroup OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointEquiv.CM

def comapEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (H : Subgroup B) :
    H.comap e.toMonoidHom ≃* H where
  toFun x := ⟨e x.val, x.property⟩
  invFun x := ⟨e.symm x.val, by
    change e (e.symm x.val) ∈ H
    rw [e.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (e.map_mul x.val y.val)

local instance parameterPropertiesPullbackMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Over.pullback f).Monoidal := Over.instBraidedPullback.toMonoidal

variable {S : Scheme} (G : Grp (Over S)) (P : Over S)

local instance : GrpObj G.X := G.grp
local instance : GrpObj ((Over.pullback P.hom).obj G.X) :=
  ((Over.pullback P.hom).mapGrp.obj G).grp

theorem fromParameter_killed
    (H : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).mapGrp.obj G).X (Over.mk (𝟙 P.left)))
    (n : ℕ) (h : H.KilledBy n) : (ParameterPointTo.CM.RelativeSubgroup.fromParameter G P H).KilledBy n := by
  intro T t a ha
  apply (ParameterPointEquiv.CM.pointEquiv G t).injective
  exact (map_pow (ParameterPointEquiv.CM.pointEquiv G t) a n).trans
    ((h (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t) (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase _) (ParameterPointEquiv.CM.pointEquiv G t a) ha).trans (ParameterPointEquiv.CM.pointEquiv G t).map_one.symm)

theorem toParameter_type (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) (M : Type) [AddCommGroup M]
    (h : F.HasModuleType M) : (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F).HasModuleType M := by
  intro k _ _ b t
  exact (h k (b ≫ P.hom) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P (Over.mk b))).map (fun e =>
    (comapEquiv (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (Over.mk b)).symm
      (F.points ((Over.map P.hom).obj (Over.mk b)) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P (Over.mk b)))).trans e)

theorem fromParameter_type
    (H : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).mapGrp.obj G).X (Over.mk (𝟙 P.left)))
    (M : Type) [AddCommGroup M] (h : H.HasModuleType M) : (ParameterPointTo.CM.RelativeSubgroup.fromParameter G P H).HasModuleType M := by
  intro k _ _ b t
  exact (h k t.left (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t))).map (fun e =>
    (comapEquiv (ParameterPointEquiv.CM.pointEquiv G t) (H.points (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t) (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)))).trans e)

theorem toParameter_supported (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) (p : G.X ⟶ G.X)
    (h : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn F p) :
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F) ((Over.pullback P.hom).map p) := by
  intro U t x hx
  apply (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm.injective
  exact (BaseChangeEvaluation.CM.pointsEquiv_map P.hom U p x).trans
    (h ((Over.map P.hom).obj U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U)
      ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm x) hx)

theorem fromParameter_supported
    (H : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).mapGrp.obj G).X (Over.mk (𝟙 P.left)))
    (p : G.X ⟶ G.X) (h : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn H ((Over.pullback P.hom).map p)) :
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (ParameterPointTo.CM.RelativeSubgroup.fromParameter G P H) p := by
  intro T t a ha
  apply (ParameterPointEquiv.CM.pointEquiv G t).injective
  exact (ParameterPointEquiv.CM.parameterize_map G t a p).trans
    (h (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t) (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase _) (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G t a) ha)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterSubgroupProperties.CM
