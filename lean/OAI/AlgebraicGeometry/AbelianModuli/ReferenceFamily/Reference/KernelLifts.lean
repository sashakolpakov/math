import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel
import OAI.RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicTranslation

/-! # Kernel Lifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! Every complex point of the constructed lattice isogeny's kernel
comes from a vector of the original integral dual lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    (p : IsogenyKernel.ReferenceLatticeIsogeny M D)

theorem IsogenyKernel.ReferenceLatticeIsogeny.exists_dual_lattice_lift (a : p.isogeny.kernelAt (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) :
    ∃ v : F.dualLattice, M.period (QuotientAddGroup.mk v.val) = a.val := by
  obtain ⟨v, hv⟩ := F.latticeKernelLift_surjective hP (p.complexKernelEquiv.symm a).toAdd
  refine ⟨v, ?_⟩
  have h := congrArg (fun t => (p.complexKernelEquiv (Multiplicative.ofAdd t)).val) hv
  exact h.trans (congrArg Subtype.val (p.complexKernelEquiv.apply_symm_apply a))

theorem IsogenyKernel.ReferenceLatticeIsogeny.kernel_translation_preserves (L : HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hL : ∀ v : F.dualLattice,
      Nonempty ((L.pullback (RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian
        (M.period (QuotientAddGroup.mk v.val))).left).sheaf ≅ L.sheaf))
    (a : p.isogeny.kernelAt (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) :
    Nonempty ((L.pullback (RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian a.val).left).sheaf ≅ L.sheaf) := by
  obtain ⟨v, hv⟩ := p.exists_dual_lattice_lift a
  rw [← hv]
  exact hL v

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
