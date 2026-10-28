import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed

/-! # Kernel Iso Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.KernelIsoTransport

noncomputable section

/-! Transport the complete all-test kernel through source and target
isomorphisms. The embedded subgroup is transported explicitly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed.Construction

variable {S : Scheme.{u}} {A A' B B' H : Over S} [GrpObj B] [GrpObj B']

theorem prescribedKernel_isos (f : A ⟶ B) (i : H ⟶ A)
    (hf : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f i) (a : A' ≅ A) (b : B ≅ B') [IsMonHom b.hom] :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (a.hom ≫ f ≫ b.hom) (i ≫ a.inv) := by
  intro T t
  constructor
  · intro ht
    have ht' : (t ≫ a.hom) ≫ f = 1 := by
      apply (cancel_mono b.hom).mp
      simpa only [Category.assoc, MonObj.one_comp] using ht
    obtain ⟨h, hh, hu⟩ := (hf T (t ≫ a.hom)).mp ht'
    refine ⟨h, ?_, ?_⟩
    · change h ≫ (i ≫ a.inv) = t
      rw [← Category.assoc, hh, Category.assoc, a.hom_inv_id, Category.comp_id]
    · intro h' hh'
      apply hu
      have he := congrArg (fun x => x ≫ a.hom) hh'
      simpa only [Category.assoc, a.inv_hom_id, Category.comp_id] using he
  · rintro ⟨h, hh, hu⟩
    have he := congrArg (fun x => x ≫ a.hom) hh
    have he' : h ≫ i = t ≫ a.hom := by
      simpa only [Category.assoc, a.inv_hom_id, Category.comp_id] using he
    have ht' := (hf T (t ≫ a.hom)).mpr ⟨h, he', fun h' hh' => by
      apply hu
      rw [← Category.assoc, hh', Category.assoc, a.hom_inv_id, Category.comp_id]⟩
    calc
      t ≫ (a.hom ≫ f ≫ b.hom) = ((t ≫ a.hom) ≫ f) ≫ b.hom := by simp only [Category.assoc]
      _ = 1 := by rw [ht', MonObj.one_comp]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.KernelIsoTransport
