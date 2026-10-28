import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.SubgroupModel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison

/-! # Model Descent -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.ModelDescent

noncomputable section

/-! A subgroup model over its parameter scheme gives a model of the
original family, with the original all-test membership predicate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} (G : Grp (Over S)) (P : Over S)

theorem terminalParameterMap_eq {U : Over P.left}
    (a b : U ⟶ Over.mk (𝟙 P.left)) : a = b := by
  apply Over.OverMorphism.ext
  exact (Category.comp_id a.left).symm.trans
    (a.w.trans (b.w.symm.trans (Category.comp_id b.left)))

def parameterArrow {X : Over S} (t : X ⟶ P) {C : Over P.left}
    (z : X ⟶ (Over.map P.hom).obj C)
    (hz : z ≫ AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P C = t) : AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t ⟶ C :=
  Over.homMk z.left (congrArg Over.Hom.left hz)

theorem parameterArrow_map {X : Over S} (t : X ⟶ P) {C : Over P.left}
    (z : X ⟶ (Over.map P.hom).obj C)
    (hz : z ≫ AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P C = t) :
    (Over.map P.hom).map (parameterArrow P t z hz) = (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).hom ≫ z :=
  Over.OverMorphism.ext (Category.id_comp z.left).symm

theorem parameterArrow_group {X : Over S} (t : X ⟶ P) {C : Over P.left}
    (z : X ⟶ (Over.map P.hom).obj C)
    (hz : z ≫ AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P C = t)
    (g : C ⟶ ((Over.pullback P.hom).mapGrp.obj G).X) :
    (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm (parameterArrow P t z hz ≫ g) =
      (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).hom ≫ z ≫ (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G C).symm g := by
  rw [AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.pullbackPointMulEquiv_symm_natural, parameterArrow_map, Category.assoc]

variable (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) (R : (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F).Model)

theorem parameterModel_base_left : R.toBase.left = R.carrier.hom :=
  (Category.comp_id R.toBase.left).symm.trans R.toBase.w

def originalParameterModel : F.Model where
  carrier := (Over.map P.hom).obj R.carrier
  toBase := AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P R.carrier
  toGroup := (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G R.carrier).symm R.toGroup
  finite := by
    change IsFinite R.carrier.hom
    rw [← parameterModel_base_left G P F R]
    exact R.finite
  flat := by
    change Flat R.carrier.hom
    rw [← parameterModel_base_left G P F R]
    exact R.flat
  finitePresentation := by
    change LocallyOfFinitePresentation R.carrier.hom
    rw [← parameterModel_base_left G P F R]
    exact R.finitePresentation
  jointly_monic X z w hbase hgroup := by
    let t := z ≫ AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P R.carrier
    let zp := parameterArrow P t z rfl
    let wp := parameterArrow P t w hbase.symm
    have h : zp = wp := by
      apply R.jointly_monic (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)
      · exact terminalParameterMap_eq P _ _
      · apply (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm.injective
        exact (parameterArrow_group G P t z rfl R.toGroup).trans
          ((congrArg (fun k => (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).hom ≫ k) hgroup).trans
            (parameterArrow_group G P t w hbase.symm R.toGroup).symm)
    exact Over.OverMorphism.ext
      (congrArg (fun k : AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t ⟶ R.carrier => k.left) h)
  points_iff X t a := by
    let b : AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t ⟶ Over.mk (𝟙 P.left) := Over.homMk t.left (Category.comp_id _)
    rw [← AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint_membership G F t a b]
    constructor
    · intro ha
      obtain ⟨h, _, hg⟩ := (R.points_iff _ _ _).mp ha
      refine ⟨(AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).inv ≫ (Over.map P.hom).map h, ?_, ?_⟩
      · rw [Category.assoc, AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint_natural, AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso_inv_base]
      · rw [Category.assoc, ← AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.pullbackPointMulEquiv_symm_natural]
        apply Eq.trans (congrArg (fun k => (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).inv ≫
          (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm k) hg)
        simp only [AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint, MulEquiv.symm_apply_apply, ← Category.assoc,
          Iso.inv_hom_id, Category.id_comp]
    · rintro ⟨z, hz, hg⟩
      apply (R.points_iff _ _ _).mpr
      refine ⟨parameterArrow P t z hz, terminalParameterMap_eq P _ _, ?_⟩
      apply (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm.injective
      exact (parameterArrow_group G P t z hz R.toGroup).trans
        ((congrArg (fun k => (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).hom ≫ k) hg).trans
          (MulEquiv.symm_apply_apply _ _).symm)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.ModelDescent
