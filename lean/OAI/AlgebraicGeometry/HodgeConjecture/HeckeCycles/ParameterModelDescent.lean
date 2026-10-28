import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.SubgroupModel

/-! # Parameter Model Descent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterModelDescent.CM

noncomputable section

/-! A finite locally free subgroup model over the parameter also
represents the original relative family. Its carrier and structure map
are the original ones, and its inclusion is the pullback projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.SubgroupModel.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterPointTo.CM.RelativeSubgroup

local instance parameterDescentPullbackMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Over.pullback f).Monoidal := Over.instBraidedPullback.toMonoidal

variable {S : Scheme} (G : Grp (Over S)) (P : Over S)

theorem parameterize_projection {T : Over S} (t : T ⟶ P) (a : T ⟶ G.X) :
    (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G t a).left ≫ pullback.fst G.X.hom P.hom = a.left := by
  have h := congrArg Over.Hom.left
    ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t)).symm_apply_apply ((AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t).hom ≫ a))
  exact h.trans (Category.id_comp a.left)

variable (H : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).mapGrp.obj G).X (Over.mk (𝟙 P.left)))
  (R : H.Model)

abbrev carrier : Over S := (Over.map P.hom).obj R.carrier

def toBase : CM.carrier G P H R ⟶ P := AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P R.carrier

def toGroup : CM.carrier G P H R ⟶ G.X := (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G R.carrier).symm R.toGroup

theorem model_base : R.toBase.left = R.carrier.hom :=
  (Category.comp_id R.toBase.left).symm.trans R.toBase.w

theorem inclusion_mono : Mono R.toGroup := by
  constructor
  intro T f h he
  exact R.jointly_monic T f h ((AbelianScheme.TateComparison.RelativePointSubgroups.testToBase_unique T _).trans (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase_unique T _).symm) he

theorem jointly_monic (T : Over S) (f h : T ⟶ CM.carrier G P H R)
    (hb : f ≫ CM.toBase G P H R = h ≫ CM.toBase G P H R)
    (hg : f ≫ CM.toGroup G P H R = h ≫ CM.toGroup G P H R) : f = h := by
  let : Mono R.toGroup := inclusion_mono G P H R
  apply Over.OverMorphism.ext
  apply (cancel_mono R.toGroup.left).mp
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg Over.Hom.left hg).trans (Category.assoc _ _ _).symm)
  · have hw : R.toGroup.left ≫ pullback.snd G.X.hom P.hom = R.carrier.hom := R.toGroup.w
    exact (Category.assoc _ _ _).trans
      ((congrArg (f.left ≫ ·) hw).trans
        ((congrArg Over.Hom.left hb).trans
          ((congrArg (h.left ≫ ·) hw.symm).trans (Category.assoc _ _ _).symm)))

def model : (ParameterPointTo.CM.RelativeSubgroup.fromParameter G P H).Model where
  carrier := CM.carrier G P H R
  toBase := CM.toBase G P H R
  toGroup := CM.toGroup G P H R
  finite := (congrArg IsFinite (model_base G P H R)).mp R.finite
  flat := (congrArg Flat (model_base G P H R)).mp R.flat
  finitePresentation := (congrArg LocallyOfFinitePresentation (model_base G P H R)).mp R.finitePresentation
  jointly_monic := CM.jointly_monic G P H R
  points_iff T t a := by
    constructor
    · intro ha
      obtain ⟨h, _, hg⟩ := (R.points_iff (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t) (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t))
        (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G t a)).mp ha
      let f : T ⟶ CM.carrier G P H R := Over.homMk h.left (by
        change h.left ≫ (R.carrier.hom ≫ P.hom) = T.hom
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ P.hom) h.w).trans t.w))
      refine ⟨f, Over.OverMorphism.ext h.w, ?_⟩
      apply Over.OverMorphism.ext
      exact (congrArg (fun z => z.left ≫ pullback.fst G.X.hom P.hom) hg).trans
        (parameterize_projection G P t a)
    · rintro ⟨f, hb, hg⟩
      let h : AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t ⟶ R.carrier := Over.homMk f.left (congrArg Over.Hom.left hb)
      apply (R.points_iff (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t) (AbelianScheme.TateComparison.RelativePointSubgroups.testToBase (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTest t))
        (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G t a)).mpr
      refine ⟨h, AbelianScheme.TateComparison.RelativePointSubgroups.testToBase_unique _ _, ?_⟩
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · exact (Category.assoc _ _ _).trans
          ((congrArg Over.Hom.left hg).trans (parameterize_projection G P t a).symm)
      · exact (h ≫ R.toGroup).w.trans (AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint G t a).w.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ParameterModelDescent.CM
