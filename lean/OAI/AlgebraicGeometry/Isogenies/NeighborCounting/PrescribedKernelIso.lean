import OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusKernelBaseChange

/-! # Prescribed Kernel Iso -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelIso

noncomputable section

/-! An exact kernel description on all test schemes identifies the
specified subgroup with the native scheme kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusKernelBaseChange.Construction

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (H : Over S) (i : H ⟶ A) [Mono i]
  (hk : ∀ (T : Over S) (a : T ⟶ A),
    a ≫ f = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a)

def prescribedKernelIso : H ≅ Picard.Homomorphisms.Kernel.Construction.kernelScheme f := by
  have hif : i ≫ f = 1 := (hk H i).mpr
    ⟨𝟙 H, Category.id_comp i,
      fun t ht => (cancel_mono i).mp (ht.trans (Category.id_comp i).symm)⟩
  let u := Picard.Homomorphisms.FrobeniusKernelBaseChange.Construction.kernelLift f i hif
  have hu : u ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f = i := Picard.Homomorphisms.FrobeniusKernelBaseChange.Construction.kernelLift_inclusion f i hif
  let v := Classical.choose ((hk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp (Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp f))
  have hv : v ≫ i = Picard.Homomorphisms.Kernel.Construction.kernelInclusion f :=
    (Classical.choose_spec ((hk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp (Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp f))).1
  refine ⟨u, v, ?_, ?_⟩
  · apply (cancel_mono i).mp
    rw [Category.assoc, hv, hu, Category.id_comp]
  · apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
    rw [Category.assoc, hu, hv, Category.id_comp]

omit [GrpObj A] [IsMonHom f] in
include i hk in
theorem prescribedKernel_finite [IsFinite H.hom] : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom := by
  let e := prescribedKernelIso f H i hk
  have : IsIso e.inv.left := (Over.forget S).map_isIso e.inv
  have h : IsFinite (e.inv.left ≫ H.hom) := inferInstance
  rw [e.inv.w] at h
  exact h

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelIso
