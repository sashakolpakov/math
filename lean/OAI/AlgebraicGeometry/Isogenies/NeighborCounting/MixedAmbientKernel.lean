import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMixedLineTransport

/-! # Mixed Ambient Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedAmbientKernel.Raw

noncomputable section

/-! Mixed-line inclusions and their ambient squares at an abstract
ordinary block, before substituting the native torsion construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMixedLineTransport

private theorem identity_tensor_mono {C : Type*} [Category C] [CartesianMonoidalCategory C]
    (M : C) {E E' : C} (f : E ⟶ E') [Mono f] : Mono ((𝟙 M) ⊗ₘ f) := by
  constructor
  intro T a b h
  apply CartesianMonoidalCategory.hom_ext
  · have hh := congrArg (fun u => u ≫ fst M E') h
    simpa only [Category.assoc, tensorHom_fst, Category.comp_id] using hh
  · apply (cancel_mono f).mp
    have hh := congrArg (fun u => u ≫ snd M E') h
    simpa only [Category.assoc, tensorHom_snd] using hh

variable (k : Type) [Field k] (q : ℕ) [Fact q.Prime]
  {C H : Over (Spec (.of k))}
  (c : (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X ≅ C)
  (i : C ⟶ H) (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)

instance raw_mixed_inclusion_mono [Mono i] : Mono (((((𝟙 (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X) ⊗ₘ
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q J).hom.hom) ≫ c.hom) ≫ i)) := by
  have : IsClosedImmersion (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q J).hom.hom.left :=
    AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding_closed (Spec (.of k)) q J
  have : Mono (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q J).hom.hom := Over.mono_of_mono_left _
  have := identity_tensor_mono (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q J).hom.hom
  infer_instance

theorem raw_mixed_inclusion_ambient {A : Over (Spec (.of k))} {B : Grp (Over (Spec (.of k)))}
    (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q B) (t : H ⟶ A) (l : B.X ⟶ A)
    (hc : c.hom ≫ i ≫ t = e.inv.hom.hom ≫ l) :
    ((((𝟙 (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X) ⊗ₘ
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q J).hom.hom) ≫ c.hom) ≫ i) ≫ t = (ActiveMixedLineTransport.chosenActiveMixedLine k q e J).hom.hom ≫ l := by
  rw [Category.assoc, Category.assoc, hc]
  exact (Category.assoc _ _ _).symm

theorem raw_mixed_factor_iff {A : Over (Spec (.of k))} {B : Grp (Over (Spec (.of k)))}
    (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q B) (t : H ⟶ A) (l : B.X ⟶ A)
    (hc : c.hom ≫ i ≫ t = e.inv.hom.hom ≫ l)
    (T : Over (Spec (.of k))) (z : T ⟶ A) :
    (∃ h : T ⟶ ((AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X ⊗ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q J).X),
      h ≫ ((((𝟙 (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X) ⊗ₘ
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q J).hom.hom) ≫ c.hom) ≫ i) ≫ t = z) ↔
    ∃ h : T ⟶ ((AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X ⊗ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q J).X),
      h ≫ (ActiveMixedLineTransport.chosenActiveMixedLine k q e J).hom.hom ≫ l = z :=
  Iff.of_eq (congrArg (fun u => ∃ h : T ⟶
    ((AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X ⊗ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q J).X), h ≫ u = z)
    (raw_mixed_inclusion_ambient k q c i J e t l hc))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedAmbientKernel.Raw
