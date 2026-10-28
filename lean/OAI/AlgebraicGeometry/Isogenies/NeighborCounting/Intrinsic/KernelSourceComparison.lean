import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport

/-! # Kernel Source Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelSourceComparison

noncomputable section

/-! An equality of the actual full kernel functors gives equality of
kernels after the prescribed source and target isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison

universe u

variable {S : Scheme.{u}} {d : ℕ} {A A' B B' C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S}
  (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A' B') (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (e : A.scheme ≅ A'.scheme) [IsMonHom e.hom]
  (t : B.scheme ≅ C.scheme) [IsMonHom t.hom]
  (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A' C)

theorem sameKernel_of_sourceComparison
    (h : AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel p.hom) = AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom)
    (hg : g.hom = e.inv ≫ f.hom ≫ t.hom) : QuotientComparison.SameKernel p g := by
  intro T x
  have hk := congrArg
    (fun H : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme (Over.mk (𝟙 S)) =>
      (x ≫ e.inv) ∈ H.points T (Over.homMk T.hom (Category.comp_id T.hom))) h
  change (((x ≫ e.inv) ≫ e.hom) ≫ p.hom = 1) = ((x ≫ e.inv) ≫ f.hom = 1) at hk
  rw [Category.assoc x e.inv e.hom, e.inv_hom_id, Category.comp_id] at hk
  change x ≫ p.hom = 1 ↔ x ≫ g.hom = 1
  rw [hg, ← Category.assoc x e.inv, ← Category.assoc (x ≫ e.inv) f.hom,
    ← MonObj.one_comp t.hom, cancel_mono]
  exact iff_of_eq hk

omit [IsMonHom e.hom] in
theorem sameKernel_of_sourceComparison_eq
    (k : A.scheme ⟶ A'.scheme) [IsMonHom k] (he : e.hom = k)
    (h : AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback k (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel p.hom) = AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom)
    (hg : g.hom = e.inv ≫ f.hom ≫ t.hom) : QuotientComparison.SameKernel p g := by
  subst k
  exact sameKernel_of_sourceComparison p f e t g h hg

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelSourceComparison
