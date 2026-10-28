import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernels

/-! # Mixed Etale Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedEtaleTransport

noncomputable section

/-! Recover the mixed active kernel from the one-step kernel on the
target etale plane and the actual plane and subgroup transport squares.
The kernel of the source etale restriction is a conclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernels

variable {S : Scheme.{u}} {E E' H H' C : Over S} [GrpObj C]

theorem prescribedKernel_transport
    (v : E ≅ E') (w : H ≅ H') (i : H ⟶ E) (i' : H' ⟶ E')
    [Mono i] [Mono i'] (hi : i ≫ v.hom = w.hom ≫ i')
    (g : E' ⟶ C) (hg : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel g i') :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (v.hom ≫ g) i := by
  intro T a
  constructor
  · intro ha
    obtain ⟨c, hc, _⟩ := (hg T (a ≫ v.hom)).mp ((Category.assoc _ _ _).trans ha)
    refine ⟨c ≫ w.inv, ?_, ?_⟩
    · apply (cancel_mono v.hom).mp
      rw [Category.assoc, hi, Category.assoc c, w.inv_hom_id_assoc]
      exact hc
    · intro b hb
      apply (cancel_mono i).mp
      apply (cancel_mono v.hom).mp
      rw [hb, Category.assoc, hi, Category.assoc c, w.inv_hom_id_assoc]
      exact hc.symm
  · rintro ⟨b, hb, _⟩
    have hk : i' ≫ g = 1 := AbelianScheme.FrobeniusKernel.Prescribed.Construction.prescribedKernel_kills g i' hg
    rw [← hb, Category.assoc, ← Category.assoc i, hi, Category.assoc,
      hk, MonObj.comp_one, MonObj.comp_one]

variable {A B M : Over S} [GrpObj A] [GrpObj B] [GrpObj M] [GrpObj E]

/-- Both comparison squares concern the actual first quotient and the
native etale subgroup. Only the second quotient's one-step kernel is input. -/
theorem mixed_kernel_from_target_etale
    (b : M ⊗ E ⟶ A) (f : A ⟶ B) (g : B ⟶ C)
    [IsMonHom b] [IsMonHom f]
    (hkill : MixedKernels.multiplicativeInclusion ≫ b ≫ f = 1)
    (j : E' ⟶ B) (v : E ≅ E') (w : H ≅ H')
    (i : H ⟶ E) (i' : H' ⟶ E') [Mono i] [Mono i']
    (hplane : MixedKernels.etaleImage b f = v.hom ≫ j)
    (hline : i ≫ v.hom = w.hom ≫ i')
    (hsecond : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (j ≫ g) i') :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (b ≫ f ≫ g) (𝟙 M ⊗ₘ i) := by
  apply MixedKernels.active_composite_prescribedKernel b f g hkill i
  rw [hplane, Category.assoc]
  exact prescribedKernel_transport v w i i' hline (j ≫ g) hsecond

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedEtaleTransport
