import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePointSubgroups

/-! # Parameter Point To -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo.CM.Naturality

/-! The passage from a test scheme with a parameter point to a test
over the parameter preserves the group law and commutes with every
further test map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePointSubgroups

variable {S : Scheme} (G : Grp (Over S)) {P T U : Over S}

local instance parameterNaturalityPullbackMonoidal : (Over.pullback P.hom).Monoidal :=
  Over.instBraidedPullback.toMonoidal

local instance : GrpObj G.X := G.grp
local instance : GrpObj ((Over.pullback P.hom).obj G.X) :=
  ((Over.pullback P.hom).mapGrp.obj G).grp

def parameterizeMul (t : T ⟶ P) :
    (T ⟶ G.X) →* (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t ⟶ ((Over.pullback P.hom).mapGrp.obj G).X) where
  toFun := AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G t
  map_one' :=
    (congrArg (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t))
      (MonObj.comp_one (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).hom)).trans
        (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).map_one
  map_mul' x y :=
    (congrArg (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t))
      (MonObj.comp_mul (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).hom x y)).trans
        ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).map_mul _ _)

def parameterTestMap (f : U ⟶ T) (t : T ⟶ P) : AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest (f ≫ t) ⟶ AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t :=
  Over.homMk f.left rfl

theorem parameterize_natural (f : U ⟶ T) (t : T ⟶ P) (x : T ⟶ G.X) :
    AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G (f ≫ t) (f ≫ x) = parameterTestMap f t ≫ AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G t x := by
  apply (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest (f ≫ t))).symm.injective
  calc
    _ = (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso (f ≫ t)).hom ≫ (f ≫ x) :=
      (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest (f ≫ t))).symm_apply_apply _
    _ = (Over.map P.hom).map (parameterTestMap f t) ≫ ((AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).hom ≫ x) := by
      apply Over.OverMorphism.ext
      change (𝟙 _ ≫ (f.left ≫ x.left)) = f.left ≫ (𝟙 _ ≫ x.left)
      simp only [Category.id_comp]
    _ = (Over.map P.hom).map (parameterTestMap f t) ≫
        (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G t x) :=
      congrArg ((Over.map P.hom).map (parameterTestMap f t) ≫ ·)
        ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm_apply_apply _).symm
    _ = _ := (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.pullbackPointMulEquiv_symm_natural P.hom G
      (parameterTestMap f t) (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G t x)).symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo.CM.Naturality

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo.CM.Roundtrip

/-! Returning an actual point over the parameter to its original test
scheme recovers the point through the canonical identity-on-schemes
comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePointSubgroups

local instance parameterRoundtripMonoidal {X Y : Scheme} (f : X ⟶ Y) : (Over.pullback f).Monoidal :=
  Over.instBraidedPullback.toMonoidal

variable {S : Scheme} (G : Grp (Over S)) (P : Over S) (U : Over P.left)

def returnTestIso : AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U) ≅ U :=
  Over.isoMk (Iso.refl U.left) (by exact Category.id_comp U.hom)

theorem parameterize_roundtrip (x : U ⟶ ((Over.pullback P.hom).mapGrp.obj G).X) :
    AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U) ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm x) =
      (returnTestIso P U).hom ≫ x := by
  apply (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U))).symm.injective
  calc
    _ = (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U)).hom ≫
        (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm x :=
      (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U))).symm_apply_apply _
    _ = (Over.map P.hom).map (returnTestIso P U).hom ≫
        (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm x := by
      apply Over.OverMorphism.ext
      rfl
    _ = _ := (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.pullbackPointMulEquiv_symm_natural P.hom G (returnTestIso P U).hom x).symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo.CM.Roundtrip

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo.CM.RelativeSubgroup

/-! Relative subgroup families over a parameter are equivalent to
subgroups of the actual base-changed group over that parameter. Both
directions use the original membership predicates on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePointSubgroups
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo.CM.Naturality OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo.CM.Roundtrip

local instance relativeParameterPullbackMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Over.pullback f).Monoidal := Over.instBraidedPullback.toMonoidal

variable {S : Scheme} (G : Grp (Over S)) (P : Over S)

local instance : GrpObj G.X := G.grp
local instance : GrpObj ((Over.pullback P.hom).obj G.X) :=
  ((Over.pullback P.hom).mapGrp.obj G).grp

def fromParameter
    (H : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).mapGrp.obj G).X (Over.mk (𝟙 P.left))) :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P where
  points T t := (H.points (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t) (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t))).comap (Naturality.parameterizeMul G t)
  naturality := by
    intro T U f t x hx
    have hh := H.naturality (Naturality.parameterTestMap f t) (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t))
      (show AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G t x ∈ H.points (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t) (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)) from hx)
    have ht : Naturality.parameterTestMap f t ≫ AbelianScheme.TateComparison.RelativePointSubgroups.testToBase (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t) = AbelianScheme.TateComparison.RelativePointSubgroups.testToBase (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest (f ≫ t)) :=
      AbelianScheme.TateComparison.RelativePointSubgroups.testToBase_unique _ _
    rw [ht] at hh
    change AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G (f ≫ t) (f ≫ x) ∈
      H.points (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest (f ≫ t)) (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest (f ≫ t)))
    exact (Naturality.parameterize_natural G f t x).symm ▸ hh

theorem from_to (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) :
    fromParameter G P (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F) = F := by
  ext T t x
  exact AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint_membership G F t x (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t))

theorem to_from
    (H : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).mapGrp.obj G).X (Over.mk (𝟙 P.left))) :
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P (fromParameter G P H) = H := by
  ext U t x
  change AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U) ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm x) ∈
      H.points (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U)) (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase _) ↔ x ∈ H.points U t
  rw [Roundtrip.parameterize_roundtrip]
  have ht : (Roundtrip.returnTestIso P U).hom ≫ t = AbelianScheme.TateComparison.RelativePointSubgroups.testToBase (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U)) :=
    AbelianScheme.TateComparison.RelativePointSubgroups.testToBase_unique _ _
  rw [← ht]
  exact AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.relativeSubgroup_membership_iso H (Roundtrip.returnTestIso P U) t x

def subgroupEquiv : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P ≃
    AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).mapGrp.obj G).X (Over.mk (𝟙 P.left)) where
  toFun := AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P
  invFun := fromParameter G P
  left_inv := from_to G P
  right_inv := to_from G P

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo.CM.RelativeSubgroup

end

end OAI
