import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange

/-! # Subgroup Model -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.SubgroupModel.Construction

noncomputable section

/-!
The original finite locally free subgroup model represents the family
after passing to its parameter scheme. Its carrier and structure map
remain the original ones; the inclusion is the ordinary pullback lift.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} (G : Grp (Over S)) (P : Over S)
  (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) (R : F.Model)

def parameterModelCarrier : Over P.left := Over.mk R.toBase.left

def parameterModelToGroup : parameterModelCarrier G P F R ⟶ ((Over.pullback P.hom).mapGrp.obj G).X :=
  Over.homMk (pullback.lift R.toGroup.left R.toBase.left (R.toGroup.w.trans R.toBase.w.symm))
    (pullback.lift_snd _ _ _)

def parameterModelPoint (U : Over P.left) (x : U ⟶ parameterModelCarrier G P F R) :
    (Over.map P.hom).obj U ⟶ R.carrier :=
  Over.homMk x.left (by
    change x.left ≫ R.carrier.hom = U.hom ≫ P.hom
    exact (congrArg (fun k : R.carrier.left ⟶ S => x.left ≫ k) R.toBase.w.symm).trans
      ((Category.assoc x.left R.toBase.left P.hom).symm.trans
        (congrArg (fun k => k ≫ P.hom) x.w)))

theorem parameterModelPoint_base (U : Over P.left) (x : U ⟶ parameterModelCarrier G P F R) :
    parameterModelPoint G P F R U x ≫ R.toBase = Relative.ParameterBaseChange.Construction.parameterBasePoint P U :=
  Over.OverMorphism.ext x.w

theorem parameterModelPoint_group (U : Over P.left) (x : U ⟶ parameterModelCarrier G P F R) :
    (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm (x ≫ parameterModelToGroup G P F R) =
      parameterModelPoint G P F R U x ≫ R.toGroup := by
  apply Over.OverMorphism.ext
  change (x.left ≫ pullback.lift R.toGroup.left R.toBase.left _) ≫
    pullback.fst G.X.hom P.hom = x.left ≫ R.toGroup.left
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k : R.carrier.left ⟶ G.X.left => x.left ≫ k)
      (pullback.lift_fst R.toGroup.left R.toBase.left (R.toGroup.w.trans R.toBase.w.symm)))

theorem parameterModelToGroup_mono : Mono (parameterModelToGroup G P F R) := by
  constructor
  intro U x y hxy
  have h : parameterModelPoint G P F R U x = parameterModelPoint G P F R U y := by
    apply R.jointly_monic ((Over.map P.hom).obj U)
    · exact (parameterModelPoint_base G P F R U x).trans (parameterModelPoint_base G P F R U y).symm
    · exact (parameterModelPoint_group G P F R U x).symm.trans
        ((congrArg (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm hxy).trans
          (parameterModelPoint_group G P F R U y))
  exact Over.OverMorphism.ext
    (congrArg (fun k : (Over.map P.hom).obj U ⟶ R.carrier => k.left) h)

def relativeSubgroupOverParameter_model : (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F).Model where
  carrier := parameterModelCarrier G P F R
  toBase := Over.homMk R.toBase.left (Category.comp_id _)
  toGroup := parameterModelToGroup G P F R
  finite := R.finite
  flat := R.flat
  finitePresentation := R.finitePresentation
  jointly_monic _ _ _ _ hh := by
    let := parameterModelToGroup_mono G P F R
    exact (cancel_mono (parameterModelToGroup G P F R)).mp hh
  points_iff U t a := by
    change (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm a ∈
      F.points ((Over.map P.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint P U) ↔ _
    constructor
    · intro ha
      obtain ⟨x, hbase, hgroup⟩ := (R.points_iff _ _ _).mp ha
      let z : U ⟶ parameterModelCarrier G P F R :=
        Over.homMk x.left (congrArg Over.Hom.left hbase)
      refine ⟨z, ?_, ?_⟩
      · apply Over.OverMorphism.ext
        exact z.w.trans (t.w.symm.trans (Category.comp_id t.left))
      · apply (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm.injective
        exact (parameterModelPoint_group G P F R U z).trans hgroup
    · rintro ⟨x, _, hx⟩
      apply (R.points_iff _ _ _).mpr
      refine ⟨parameterModelPoint G P F R U x, parameterModelPoint_base G P F R U x, ?_⟩
      exact (parameterModelPoint_group G P F R U x).symm.trans
        (congrArg (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm hx)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.SubgroupModel.Construction
