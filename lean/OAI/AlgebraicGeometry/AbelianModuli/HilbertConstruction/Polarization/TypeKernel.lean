import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.EtaleKernelType
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.PresentationCancellation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.DegreeLoci
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Degree

/-! # Type Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.TypeKernel

noncomputable section

/-! The original polarization type is exactly the geometric kernel
group together with the full finite-flat degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
open scoped BigOperators _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

theorem hasPolarizationType_iff_kernelData
    {S : Scheme.{u}} {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}
    (p : Abelian.Schemes.AbelianScheme.Isogeny A B) (δ : Fin g → ℕ) :
    p.HasPolarizationType δ ↔
      (∀ s : S, (Picard.PoincareBundle.Kernel.Scheme.kernelObject p.hom).hom.finrank s = (∏ i, δ i) ^ 2) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S),
        Nonempty ((Over.mk s ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject p.hom) ≃*
          Multiplicative ((∀ i : Fin g, ZMod (δ i)) × (∀ i : Fin g, ZMod (δ i)))) := by
  have : LocallyOfFinitePresentation p.hom.left :=
    Finite.PresentationCancellation.locallyFinitePresentation_of_comp_of_locallyFiniteType
      (f := p.hom.left) (g := B.scheme.hom)
      (by rw [p.hom.w]; infer_instance) inferInstance
  constructor
  · intro hp
    refine ⟨fun s => (Picard.PoincareBundle.Kernel.Degree.kernel_rank p.hom s).trans (hp.degree _), ?_⟩
    intro K hK hclosed s
    obtain ⟨e⟩ := hp.geometricKernel K s
    exact ⟨(Picard.PoincareBundle.Kernel.Scheme.kernelPointsMulEquiv p.hom (Over.mk s)).trans e⟩
  · rintro ⟨hd, hg⟩
    constructor
    · intro b
      exact (AbelianScheme.IsogenyQuotient.Relative.DegreeLoci.Construction.finiteFlatDegree_eq_base_degree p.hom b).trans
        ((Picard.PoincareBundle.Kernel.Degree.kernel_rank p.hom (B.scheme.hom b)).symm.trans (hd _))
    · intro K hK hclosed s
      obtain ⟨e⟩ := hg K s
      exact ⟨(Picard.PoincareBundle.Kernel.Scheme.kernelPointsMulEquiv p.hom (Over.mk s)).symm.trans e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.TypeKernel
