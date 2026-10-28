import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.EquivalenceRelation

/-! # Etale Kernel Pair -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleKernelPair

noncomputable section

/-! A flat finitely presented quotient with an etale kernel-pair
projection is etale. Its diagonal is the identity section of the
represented equivalence relation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem etale_of_etale_kernelPair {R X Q : Scheme.{0}} (s t : R ⟶ X) (π : X ⟶ Q)
    [Etale s] [Flat π] [LocallyOfFinitePresentation π]
    (e : CategoryTheory.EquivalenceRelation s t) (h : IsKernelPair π s t) : Etale π := by
  let : IsSplitMono e.r := ⟨⟨⟨s, e.reflexivity₁⟩⟩⟩
  have hrs : Etale (e.r ≫ s) := e.reflexivity₁.symm ▸ inferInstanceAs (Etale (𝟙 X))
  let : Etale e.r := Etale.of_comp e.r s
  let : IsOpenImmersion e.r := IsOpenImmersion.of_flat_of_mono e.r
  have hdiag : e.r ≫ h.isoPullback.hom = pullback.diagonal π := by
    apply pullback.hom_ext
    · rw [Category.assoc, h.isoPullback_hom_fst, e.reflexivity₁, pullback.diagonal_fst]
    · rw [Category.assoc, h.isoPullback_hom_snd, e.reflexivity₂, pullback.diagonal_snd]
  have : IsOpenImmersion (pullback.diagonal π) := by
    rw [← hdiag]
    infer_instance
  exact Etale.of_formallyUnramified_of_flat π

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleKernelPair
