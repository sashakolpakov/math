import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AmbientComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockStability

/-! # Stability -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Stability.Construction

noncomputable section

/-!
Turn all-test subgroup stability into the exact native scheme equation
used to descend the integral action through ReferenceFamily's quotient family.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {dim : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme dim S) (P : Over S)
  (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P) (R : F.Model)

/-- The canonical inclusion into ReferenceFamily's ordinary pullback family. -/
def nativeSubgroupInclusion : (Subgroup.Construction.subgroupGroupScheme F R).X ⟶ (A.pullback P.hom).scheme :=
  (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom ≫ (AmbientComparison.Construction.ambientPullbackIso P A).hom

theorem nativeSubgroupInclusion_isMonHom : IsMonHom (nativeSubgroupInclusion A P F R) := by
  have : IsMonHom (AmbientComparison.Construction.ambientPullbackIso P A).hom := AmbientComparison.Construction.ambientPullbackIso_isMonHom P A
  have : IsMonHom (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom :=
    (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.isMonHom_hom
  exact inferInstanceAs
    (IsMonHom ((Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom ≫ (AmbientComparison.Construction.ambientPullbackIso P A).hom))

theorem nativeSubgroupInclusion_closedImmersion :
    IsClosedImmersion (nativeSubgroupInclusion A P F R).left := by
  have : IsClosedImmersion (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom.left :=
    Kernel.Inclusion.Construction.subgroupInclusion_closedImmersion F R
  have : IsIso (AmbientComparison.Construction.ambientPullbackIso P A).hom.left :=
    (Over.forget P.left).map_isIso (AmbientComparison.Construction.ambientPullbackIso P A).hom
  exact inferInstanceAs
    (IsClosedImmersion ((Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom.left ≫ (AmbientComparison.Construction.ambientPullbackIso P A).hom.left))

theorem nativeSubgroupInclusion_projection :
    (nativeSubgroupInclusion A P F R).left ≫ pullback.fst A.scheme.hom P.hom = R.toGroup.left := by
  change ((lift R.toBase R.toGroup).left ≫ (pullbackSymmetry P.hom A.scheme.hom).hom) ≫
    pullback.fst A.scheme.hom P.hom = R.toGroup.left
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact congrArg (fun a => a.left) (lift_snd R.toBase R.toGroup)

set_option backward.isDefEq.respectTransparency false in
/-- Restrict a stable endomorphism to the actual subgroup model. The
resulting square is an equality of morphisms over the parameter scheme. -/
theorem native_subgroup_stability
    (b : A.scheme ⟶ A.scheme) (hstable : Action.Construction.RelativeSubgroupStable F b) :
    ∃ r : (Subgroup.Construction.subgroupGroupScheme F R).X ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
      nativeSubgroupInclusion A P F R ≫ (Over.pullback P.hom).map b =
        r ≫ nativeSubgroupInclusion A P F R := by
  have hi : R.toGroup ∈ F.points R.carrier R.toBase :=
    (R.points_iff _ _ _).mpr ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩
  obtain ⟨r, hrbase, hrgroup⟩ := (R.points_iff _ _ _).mp
    (hstable R.carrier R.toBase R.toGroup hi)
  let rP : (Subgroup.Construction.subgroupGroupScheme F R).X ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X :=
    Over.homMk r.left (congrArg (fun a => a.left) hrbase)
  refine ⟨rP, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hb : ((Over.pullback P.hom).map b).left ≫ pullback.fst A.scheme.hom P.hom =
        pullback.fst A.scheme.hom P.hom ≫ b.left := pullback.lift_fst _ _ _
    have hiP := nativeSubgroupInclusion_projection A P F R
    change ((nativeSubgroupInclusion A P F R).left ≫ ((Over.pullback P.hom).map b).left) ≫
      pullback.fst A.scheme.hom P.hom =
        (r.left ≫ (nativeSubgroupInclusion A P F R).left) ≫ pullback.fst A.scheme.hom P.hom
    rw [Category.assoc, hb, ← Category.assoc, hiP, Category.assoc, hiP]
    exact (congrArg (fun a => a.left) hrgroup).symm
  · exact (nativeSubgroupInclusion A P F R ≫ (Over.pullback P.hom).map b).w.trans
      (rP ≫ nativeSubgroupInclusion A P F R).w.symm

set_option backward.isDefEq.respectTransparency false in
/-- The scheme equation needed by quotient action descent follows from
the constructed subgroup restriction and the quotient's kernel equation. -/
theorem native_stable_kernel_equation
    (b : A.scheme ⟶ A.scheme) (hstable : Action.Construction.RelativeSubgroupStable F b)
    {B : Over P.left} [GrpObj B] (f : (A.pullback P.hom).scheme ⟶ B)
    (hkernel : nativeSubgroupInclusion A P F R ≫ f = 1) :
    nativeSubgroupInclusion A P F R ≫ (Over.pullback P.hom).map b ≫ f = 1 := by
  obtain ⟨r, hr⟩ := native_subgroup_stability A P F R b hstable
  rw [← Category.assoc, hr, Category.assoc, hkernel, MonObj.comp_one]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Stability.Construction
