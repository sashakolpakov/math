import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IdentityModeledQuotient
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelPoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Identity Quotient Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IdentityQuotientKernel

noncomputable section

/-! The normalized integral quotient has the original relative
subgroup as its full kernel on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem identitySourceBaseChangePoint (T : Over S) (x : T ⟶ A.scheme) :
    A.baseChangePointsMulEquiv (𝟙 S) T (x ≫ A.pullbackIdIso.inv) =
      (Over.mapId S).hom.app T ≫ x := by
  apply Over.OverMorphism.ext
  change (x.left ≫ A.pullbackIdIso.inv.left) ≫ pullback.fst A.scheme.hom (𝟙 S) =
    𝟙 T.left ≫ x.left
  have hp : A.pullbackIdIso.inv.left ≫ pullback.fst A.scheme.hom (𝟙 S) = 𝟙 A.scheme.left :=
    (congrArg (fun f : (A.pullback (𝟙 S)).scheme.left ⟶ A.scheme.left =>
      A.pullbackIdIso.inv.left ≫ f) A.pullbackIdIso_hom_left).symm.trans
        (congrArg (fun f : A.scheme ⟶ A.scheme => f.left) A.pullbackIdIso.inv_hom_id)
  exact (Category.assoc x.left A.pullbackIdIso.inv.left (pullback.fst A.scheme.hom (𝟙 S))).trans
    ((congrArg (fun f : A.scheme.left ⟶ A.scheme.left => x.left ≫ f) hp).trans
      ((Category.comp_id x.left).trans (Category.id_comp x.left).symm))

theorem identityParameterPoint (T : Over S) (t : T ⟶ Over.mk (𝟙 S)) :
    (Over.mapId S).hom.app T ≫ t = AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint (Over.mk (𝟙 S)) T := by
  apply Over.OverMorphism.ext
  change 𝟙 T.left ≫ t.left = T.hom
  exact (Category.id_comp t.left).trans ((Category.comp_id t.left).symm.trans t.w)

variable {A} {n : ℕ} {F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme (Over.mk (𝟙 S))} {R : F.Model}
  (Q : Intrinsic.ModeledQuotient.Lifts.NativeModeledQuotient A (Over.mk (𝟙 S)) F R n)

theorem identitySourceIsogeny_membership (T : Over S) (t : T ⟶ Over.mk (𝟙 S))
    (x : T ⟶ A.scheme) :
    x ≫ Q.identitySourceIsogeny.hom = 1 ↔ x ∈ F.points T t := by
  change x ≫ (A.pullbackIdIso.inv ≫ Q.isogeny.hom) = 1 ↔ _
  rw [← Category.assoc]
  have h := AbelianScheme.IsogenyQuotient.Intrinsic.KernelPoints.Construction.nativeQuotient_kernel_membership A (Over.mk (𝟙 S)) F R
    Q.isogeny Q.kernel T (x ≫ A.pullbackIdIso.inv)
  apply h.trans
  change A.baseChangePointsMulEquiv (𝟙 S) T (x ≫ A.pullbackIdIso.inv) ∈
    F.points ((Over.map (𝟙 S)).obj T) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint (Over.mk (𝟙 S)) T) ↔ _
  rw [identitySourceBaseChangePoint, ← identityParameterPoint T t]
  exact AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.relativeSubgroup_membership_iso F ((Over.mapId S).app T) t x

theorem identitySourceIsogeny_nativeKernel : AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel Q.identitySourceIsogeny.hom = F := by
  ext T t x
  exact identitySourceIsogeny_membership Q T t x

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IdentityQuotientKernel
