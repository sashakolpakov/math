import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELTransport
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.KernelIsoTransport

/-! # PEL Kernel Target Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELKernelTargetTransport

noncomputable section

/-! Full PEL target transport preserves the original embedded scheme
kernel exactly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {R : Type u} [CommRing R] {S : Scheme.{u}} {g N n : ℕ}
  {A B C : AbelianScheme.TateComparison.PEL.PELFamilyData R g N S} (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B n) (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso B C)
  {H : Over S} (i : H ⟶ A.abelian.scheme)

theorem prescribedKernel_target_transport (h : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f.isogeny.hom i) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (f.transport (AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl A) e).isogeny.hom i := by
  rw [AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.transport_hom]
  have ht := Kernel.KernelIsoTransport.prescribedKernel_isos f.isogeny.hom i h
    (Iso.refl A.abelian.scheme) e.abelian
  simpa only [AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl, Iso.refl_hom, Iso.refl_inv, Category.comp_id] using ht

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELKernelTargetTransport
