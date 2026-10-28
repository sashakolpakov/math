import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Open Unit Unramified Group -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.OpenUnitUnramifiedGroup.Geometric

noncomputable section

/-! An open identity section makes an actual group scheme formally
unramified: the diagonal is the pullback of the identity along the
group difference morphism. No flatness assumption is used. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

def groupDifference : G ⊗ G ⟶ G := (fst G G)⁻¹ * snd G G

theorem groupDifference_diagonal_isPullback :
    IsPullback (lift (𝟙 G) (𝟙 G)) (toUnit G) (groupDifference G) η[G] := by
  have hw : lift (𝟙 G) (𝟙 G) ≫ groupDifference G = toUnit G ≫ η[G] := by
    change lift (𝟙 G) (𝟙 G) ≫ groupDifference G = (1 : G ⟶ G)
    simp only [groupDifference, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, inv_mul_cancel]
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw)
  refine PullbackCone.IsLimit.mk hw (fun c => c.fst ≫ fst G G) ?_ ?_ ?_
  · intro c
    have he : c.fst ≫ fst G G = c.fst ≫ snd G G := by
      have hc : (c.fst ≫ fst G G)⁻¹ * (c.fst ≫ snd G G) = 1 := by
        simpa only [groupDifference, MonObj.comp_mul, GrpObj.comp_inv,
          MonObj.one_eq_one, MonObj.comp_one] using c.condition
      exact inv_mul_eq_one.mp hc
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.comp_id]
    · rw [Category.assoc, lift_snd, Category.comp_id]
      exact he
  · intro c
    exact Subsingleton.elim _ _
  · intro c m hm _
    have h := congrArg (fun a => a ≫ fst G G) hm
    simpa only [Category.assoc, lift_fst, Category.comp_id] using h

theorem group_formallyUnramified_of_open_unit [IsOpenImmersion η[G].left] :
    FormallyUnramified G.hom := by
  have hp : IsPullback (pullback.diagonal G.hom) G.hom (groupDifference G).left η[G].left :=
    (Over.forget S).map_isPullback (groupDifference_diagonal_isPullback G)
  let : IsOpenImmersion (pullback.diagonal G.hom) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hp.flip inferInstance
  infer_instance

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.OpenUnitUnramifiedGroup.Geometric
