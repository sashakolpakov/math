import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Stability
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.IntrinsicSubgroup
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Kernel Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelPoints.Construction

noncomputable section

/-!
The universal native quotient has the original relative kernel on every
test scheme. The same formula holds after arbitrary base change, with
points compared by the actual pullback adjunction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S) (P : Over S)
  (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P) (R : F.Model)

theorem nativeSubgroupInclusion_parameter :
    Stability.Construction.nativeSubgroupInclusion A P F R =
      (Parameter.IntrinsicSubgroup.Construction.parameterNativeSubgroupInclusion (Grp.mk A.scheme) P F R).hom.hom := rfl

theorem nativeSubgroupInclusion_points (U : Over P.left)
    (x : U ⟶ (A.pullback P.hom).scheme) :
    (∃! h : U ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
      h ≫ Stability.Construction.nativeSubgroupInclusion A P F R = x) ↔
    A.baseChangePointsMulEquiv P.hom U x ∈
      F.points ((Over.map P.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint P U) := by
  have hi := Parameter.IntrinsicSubgroup.Construction.parameterNativeSubgroup_image (Grp.mk A.scheme) P F R
  have hx : (∃ h : U ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
      h ≫ Stability.Construction.nativeSubgroupInclusion A P F R = x) ↔
      A.baseChangePointsMulEquiv P.hom U x ∈
        F.points ((Over.map P.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint P U) := by
    have he := congrArg (fun H => x ∈ H.points U
      (Over.homMk U.hom (Category.comp_id U.hom))) hi
    exact iff_of_eq he
  have : IsClosedImmersion (Stability.Construction.nativeSubgroupInclusion A P F R).left :=
    Stability.Construction.nativeSubgroupInclusion_closedImmersion A P F R
  have : Mono (Stability.Construction.nativeSubgroupInclusion A P F R) := Over.mono_of_mono_left _
  constructor
  · rintro ⟨h, hh, _⟩
    exact hx.mp ⟨h, hh⟩
  · intro h
    obtain ⟨y, hy⟩ := hx.mpr h
    exact ⟨y, hy, fun z hz =>
      (cancel_mono (Stability.Construction.nativeSubgroupInclusion A P F R)).mp (hz.trans hy.symm)⟩

theorem nativeQuotient_kernel_membership
    {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d P.left}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback P.hom) B)
    (hker : ∀ (U : Over P.left) (x : U ⟶ (A.pullback P.hom).scheme),
      x ≫ f.hom = 1 ↔ ∃! h : U ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
        h ≫ Stability.Construction.nativeSubgroupInclusion A P F R = x)
    (U : Over P.left) (x : U ⟶ (A.pullback P.hom).scheme) :
    x ≫ f.hom = 1 ↔ A.baseChangePointsMulEquiv P.hom U x ∈
      F.points ((Over.map P.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint P U) :=
  (hker U x).trans (nativeSubgroupInclusion_points A P F R U x)

theorem isogeny_pullback_kernel_membership
    {T : Scheme.{u}} {B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B C) (b : T ⟶ S)
    (U : Over T) (x : U ⟶ (B.pullback b).scheme) :
    x ≫ (f.pullback b).hom = 1 ↔ B.baseChangePointsMulEquiv b U x ≫ f.hom = 1 := by
  have hn : C.baseChangePointsMulEquiv b U (x ≫ (f.pullback b).hom) =
      B.baseChangePointsMulEquiv b U x ≫ f.hom :=
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map f.hom b U x
  constructor
  · intro hx
    exact hn.symm.trans ((congrArg (C.baseChangePointsMulEquiv b U) hx).trans
      (C.baseChangePointsMulEquiv b U).map_one)
  · intro hx
    apply (C.baseChangePointsMulEquiv b U).injective
    exact hn.trans (hx.trans (C.baseChangePointsMulEquiv b U).map_one.symm)

theorem nativeQuotient_pullback_kernel_membership
    {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d P.left}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback P.hom) B)
    (hker : ∀ (U : Over P.left) (x : U ⟶ (A.pullback P.hom).scheme),
      x ≫ f.hom = 1 ↔ ∃! h : U ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
        h ≫ Stability.Construction.nativeSubgroupInclusion A P F R = x)
    {T : Scheme.{u}} (b : T ⟶ P.left) (U : Over T)
    (x : U ⟶ ((A.pullback P.hom).pullback b).scheme) :
    x ≫ (f.pullback b).hom = 1 ↔
      A.baseChangePointsMulEquiv P.hom ((Over.map b).obj U)
        ((A.pullback P.hom).baseChangePointsMulEquiv b U x) ∈
      F.points ((Over.map P.hom).obj ((Over.map b).obj U))
        (Relative.ParameterBaseChange.Construction.parameterBasePoint P ((Over.map b).obj U)) :=
  (isogeny_pullback_kernel_membership f b U x).trans
    (nativeQuotient_kernel_membership A P F R f hker _ _)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelPoints.Construction
