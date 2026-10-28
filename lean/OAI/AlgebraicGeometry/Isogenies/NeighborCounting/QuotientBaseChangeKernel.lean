import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IdentityQuotientKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelBaseChange

/-! # Quotient Base Change Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientBaseChangeKernel.Identity

noncomputable section

/-! The generic fiber of the normalized integral quotient retains the
literal base change of the original complete relative kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelBaseChange.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IdentityQuotientKernel

universe u

variable {S T : Scheme.{u}} {g n : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  {F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme (Over.mk (𝟙 S))} {R : F.Model}
  (Q : Intrinsic.ModeledQuotient.Lifts.NativeModeledQuotient A (Over.mk (𝟙 S)) F R n) (b : T ⟶ S)

theorem identitySourceIsogeny_pullback_nativeKernel :
    AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (Q.identitySourceIsogeny.pullback b).hom =
      AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.scheme) (Over.mk b)
        (F.baseChange (Over.homMk b (Category.comp_id b))) := by
  have h := AbelianScheme.IsogenyQuotient.Intrinsic.KernelBaseChange.Construction.nativeMorphismKernel_baseChange (Grp.mk A.scheme) (Grp.mk Q.target.scheme)
    (Over.mk b) (Grp.ofHom Q.identitySourceIsogeny.hom)
  have hF := congrArg
    (fun H : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme (Over.mk (𝟙 S)) =>
      H.baseChange (show Over.mk b ⟶ Over.mk (𝟙 S) from
        Over.homMk b (Category.comp_id b)))
    (IdentityQuotientKernel.identitySourceIsogeny_nativeKernel Q)
  exact h.trans (congrArg (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.scheme) (Over.mk b)) hF)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientBaseChangeKernel.Identity
