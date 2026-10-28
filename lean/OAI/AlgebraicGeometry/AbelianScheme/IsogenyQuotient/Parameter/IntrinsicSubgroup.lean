import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GenericAmbientPullback
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.RelativeAnnihilator

/-! # Intrinsic Subgroup -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.IntrinsicSubgroup.Construction

noncomputable section

/-!
The original subgroup model embeds as a native commutative group over
the parameter. Its image is precisely the original subgroup after the
ordinary base-change point comparison.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (P : Over S)
  (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) (R : F.Model)

def parameterNativeSubgroupInclusion :
    (Subgroup.Construction.subgroupGroupScheme F R).toGrp ⟶ (Over.pullback P.hom).mapGrp.obj G := by
  let k : (Kernel.Inclusion.Construction.ambientGroupScheme G.X P).toGrp ⟶ (Over.pullback P.hom).mapGrp.obj G :=
    Grp.homMk (GenericAmbientPullback.Construction.nativeAmbientPullbackIso G P).hom
  exact (Kernel.Inclusion.Construction.subgroupInclusion F R).hom ≫ k

theorem parameterNativeSubgroupInclusion_eq :
    (parameterNativeSubgroupInclusion G P F R).hom.hom = SubgroupModel.Construction.parameterModelToGroup G P F R := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((lift R.toBase R.toGroup).left ≫ (pullbackSymmetry P.hom G.X.hom).hom) ≫
      pullback.fst G.X.hom P.hom =
        pullback.lift R.toGroup.left R.toBase.left _ ≫ pullback.fst G.X.hom P.hom
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (lift R.toBase R.toGroup).left ≫ k)
        (pullbackSymmetry_hom_comp_fst P.hom G.X.hom)).trans
          ((congrArg Over.Hom.left (lift_snd R.toBase R.toGroup)).trans
            (pullback.lift_fst R.toGroup.left R.toBase.left (R.toGroup.w.trans R.toBase.w.symm)).symm))
  · exact (parameterNativeSubgroupInclusion G P F R).hom.hom.w.trans
      (SubgroupModel.Construction.parameterModelToGroup G P F R).w.symm

instance parameterNativeSubgroupInclusion_mono :
    Mono (parameterNativeSubgroupInclusion G P F R).hom.hom :=
  (parameterNativeSubgroupInclusion_eq G P F R).symm ▸ SubgroupModel.Construction.parameterModelToGroup_mono G P F R

theorem parameterNativeSubgroup_image :
    Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup (parameterNativeSubgroupInclusion G P F R).hom.hom =
      Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F := by
  ext U t y
  have h := (SubgroupModel.Construction.relativeSubgroupOverParameter_model G P F R).points_iff U t y
  constructor
  · rintro ⟨x, hx⟩
    apply h.mpr
    refine ⟨x, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      exact x.w.trans (t.w.symm.trans (Category.comp_id t.left))
    · exact (congrArg (fun k => x ≫ k) (parameterNativeSubgroupInclusion_eq G P F R)).symm.trans hx
  · intro hy
    obtain ⟨x, _, hx⟩ := h.mp hy
    exact ⟨x, (congrArg (fun k => x ≫ k) (parameterNativeSubgroupInclusion_eq G P F R)).trans hx⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.IntrinsicSubgroup.Construction
