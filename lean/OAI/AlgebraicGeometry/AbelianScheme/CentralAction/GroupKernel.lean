import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InfinitesimalLifting
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

/-! # Group Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GroupKernel.Construction

noncomputable section

/-! The actual group-scheme kernel represents all test-scheme kernels.
A finite etale kernel forces its group homomorphism to be unramified. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]

def groupKernelScheme (f : A ⟶ B) : Over S := equalizer f (1 : A ⟶ B)

def groupKernelInclusion (f : A ⟶ B) : groupKernelScheme f ⟶ A := equalizer.ι f 1

omit [GrpObj A] in
theorem groupKernelInclusion_comp (f : A ⟶ B) :
    groupKernelInclusion f ≫ f = 1 := by
  exact (equalizer.condition f (1 : A ⟶ B)).trans (MonObj.comp_one _)

def groupKernelLift (f : A ⟶ B) {T : Over S} (x : T ⟶ A) (hx : x ≫ f = 1) :
    T ⟶ groupKernelScheme f := equalizer.lift x (hx.trans (MonObj.comp_one x).symm)

omit [GrpObj A] in
@[simp] theorem groupKernelLift_inclusion (f : A ⟶ B) {T : Over S}
    (x : T ⟶ A) (hx : x ≫ f = 1) :
    groupKernelLift f x hx ≫ groupKernelInclusion f = x := equalizer.lift_ι _ _

def groupKernelPointsEquiv (f : A ⟶ B) (T : Over S) :
    (T ⟶ groupKernelScheme f) ≃ {x : T ⟶ A // x ≫ f = 1} where
  toFun z := ⟨z ≫ groupKernelInclusion f, by
    rw [Category.assoc, groupKernelInclusion_comp, MonObj.comp_one]⟩
  invFun x := groupKernelLift f x.val x.property
  left_inv z := by apply equalizer.hom_ext; exact groupKernelLift_inclusion _ _ _
  right_inv x := Subtype.ext (groupKernelLift_inclusion _ _ _)

omit [GrpObj A] in
theorem groupKernel_isPullback (f : A ⟶ B) :
    IsPullback (groupKernelInclusion f) (toUnit (groupKernelScheme f)) f η[B] := by
  apply IsPullback.mk'
  · exact groupKernelInclusion_comp f
  · intro T a b hab _
    exact equalizer.hom_ext hab
  · intro T a b hab
    have hb : b ≫ η[B] = (1 : T ⟶ B) := by
      change b ≫ η[B] = toUnit T ≫ η[B]
      rw [toUnit_unique b (toUnit T)]
    exact ⟨groupKernelLift f a (hab.trans hb), groupKernelLift_inclusion _ _ _,
      toUnit_unique _ _⟩

omit [GrpObj A] in
theorem groupKernel_isPullback_left (f : A ⟶ B) :
    IsPullback (groupKernelInclusion f).left (groupKernelScheme f).hom f.left η[B].left :=
  (groupKernel_isPullback f).map (Over.forget S)

theorem groupHom_unramified_of_etale_kernel (f : A ⟶ B) [IsMonHom f]
    [IsFinite (groupKernelScheme f).hom] [Etale (groupKernelScheme f).hom] :
    FormallyUnramified f.left := by
  apply FormallyUnramified.of_hom_ext
  intro C D φ _ hφ a b hab hcomp
  let T : Over S := Over.mk (a ≫ A.hom)
  let aa : T ⟶ A := Over.homMk a rfl
  let bb : T ⟶ A := Over.homMk b (by
    change b ≫ A.hom = a ≫ A.hom
    rw [← f.w, ← Category.assoc, ← Category.assoc, hcomp])
  let T' : Over S := Over.mk (Spec.map φ ≫ T.hom)
  let i : T' ⟶ T := Over.homMk (Spec.map φ) rfl
  have hcomp' : aa ≫ f = bb ≫ f := Over.OverMorphism.ext hcomp
  have hred : i ≫ aa = i ≫ bb := Over.OverMorphism.ext hab
  let d := groupKernelLift f (aa / bb) (by rw [GrpObj.div_comp, hcomp', div_self'])
  let z := groupKernelLift f (1 : T ⟶ A) (MonObj.one_comp f)
  have hdz : i ≫ d = i ≫ z := by
    apply equalizer.hom_ext
    change (i ≫ d) ≫ groupKernelInclusion f = (i ≫ z) ≫ groupKernelInclusion f
    rw [Category.assoc, Category.assoc, groupKernelLift_inclusion,
      groupKernelLift_inclusion, GrpObj.comp_div, hred, div_self', MonObj.comp_one]
  have he := IsogenyQuotient.InfinitesimalLifting.Construction.finite_etale_nilpotent_hom_ext (groupKernelScheme f).hom
    φ.hom ⟨2, hφ⟩ d.left z.left (d.w.trans z.w.symm) (congrArg Over.Hom.left hdz)
  have he' : d = z := Over.OverMorphism.ext he
  have hd := congrArg (fun j => j ≫ groupKernelInclusion f) he'
  change groupKernelLift f (aa / bb) _ ≫ groupKernelInclusion f =
    groupKernelLift f 1 _ ≫ groupKernelInclusion f at hd
  rw [groupKernelLift_inclusion, groupKernelLift_inclusion, div_eq_one] at hd
  exact congrArg Over.Hom.left hd

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GroupKernel.Construction
