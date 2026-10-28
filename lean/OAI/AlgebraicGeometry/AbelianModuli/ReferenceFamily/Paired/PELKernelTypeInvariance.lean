import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELFunctor
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELKernelModuleType

/-! # PEL Kernel Type Invariance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired

noncomputable section

/-! The original full kernel module type is invariant under actual
paired PEL isomorphisms and arbitrary test-scheme pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T U : Over (Spec (.of K))}
    {A B A' B' : PEL.Objects.PELObject P iota N T}
    {f : PELQuotients.PairedPELQuotient A B n} {g : PELQuotients.PairedPELQuotient A' B' n}

def PELFunctor.PairedPELQuotientIso.forwardKernelEquiv (e : PELFunctor.PairedPELQuotientIso f g)
    (X : Over T.left) : f.forward.isogeny.kernelAt X ≃* g.forward.isogeny.kernelAt X where
  toFun x := ⟨x.val ≫ e.source.polarized.abelian.hom, by
    change (x.val ≫ e.source.polarized.abelian.hom) ≫ g.forward.isogeny.hom = 1
    have hx : x.val ≫ f.forward.isogeny.hom = 1 := x.property
    rw [Category.assoc, ← e.forward_square, ← Category.assoc, hx, MonObj.one_comp]⟩
  invFun x := ⟨x.val ≫ e.source.polarized.abelian.inv, by
    change (x.val ≫ e.source.polarized.abelian.inv) ≫ f.forward.isogeny.hom = 1
    have hx : x.val ≫ g.forward.isogeny.hom = 1 := x.property
    have he := e.symm.forward_square
    change g.forward.isogeny.hom ≫ e.target.polarized.abelian.inv =
      e.source.polarized.abelian.inv ≫ f.forward.isogeny.hom at he
    rw [Category.assoc, ← he, ← Category.assoc, hx, MonObj.one_comp]⟩
  left_inv x := Subtype.ext (by
    change (x.val ≫ e.source.polarized.abelian.hom) ≫ e.source.polarized.abelian.inv = x.val
    rw [Category.assoc, e.source.polarized.abelian.hom_inv_id, Category.comp_id])
  right_inv x := Subtype.ext (by
    change (x.val ≫ e.source.polarized.abelian.inv) ≫ e.source.polarized.abelian.hom = x.val
    rw [Category.assoc, e.source.polarized.abelian.inv_hom_id, Category.comp_id])
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val e.source.polarized.abelian.hom)

theorem PELFunctor.PairedPELQuotientIso.kernel_moduleType_iff (e : PELFunctor.PairedPELQuotientIso f g)
    (M : Type) [AddCommGroup M] :
    (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom).HasModuleType M ↔
      (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel g.forward.isogeny.hom).HasModuleType M := by
  constructor
  · intro h k _ _ b t
    obtain ⟨d⟩ := h k b t
    exact ⟨(e.forwardKernelEquiv (Over.mk b)).symm.trans d⟩
  · intro h k _ _ b t
    obtain ⟨d⟩ := h k b t
    exact ⟨(e.forwardKernelEquiv (Over.mk b)).trans d⟩

theorem PELQuotients.PairedPELQuotient.kernel_moduleType_pullback (f : PELQuotients.PairedPELQuotient A B n)
    (M : Type) [AddCommGroup M]
    (h : (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom).HasModuleType M) (b : U ⟶ T) :
    (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (f.pullback b).forward.isogeny.hom).HasModuleType M := by
  intro k _ _ c t
  obtain ⟨d⟩ := h k (c ≫ b.left) (Over.homMk (c ≫ b.left) (Category.comp_id _))
  exact ⟨(f.forward.isogeny.kernelBaseChangeEquiv b.left (Over.mk c)).trans d⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired
