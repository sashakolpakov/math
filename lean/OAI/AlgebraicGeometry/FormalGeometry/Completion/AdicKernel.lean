import Mathlib.RingTheory.AdicCompletion.Exactness

/-! # Adic Kernel -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicKernel.Construction

noncomputable section

/-!
# Completion: completion commutes with kernels of maps between finite modules

The map is the actual completion of the kernel inclusion. Its surjectivity
uses Artin--Rees exactness, factoring the original map through its image.
This is the degree-zero completion calculation for a finite cochain model.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N)

/-- Completion of the actual kernel inclusion lands in the completed differential's kernel. -/
def adicKernelMap : AdicCompletion I f.ker →ₗ[AdicCompletion I R] (AdicCompletion.map I f).ker :=
  (AdicCompletion.map I f.ker.subtype).codRestrict _ fun x => by
    change AdicCompletion.map I f (AdicCompletion.map I f.ker.subtype x) = 0
    rw [AdicCompletion.map_comp_apply]
    have h : f.comp f.ker.subtype = 0 := by ext y; exact y.property
    rw [h, AdicCompletion.map_zero, LinearMap.zero_apply]

/-- The completed kernel map is bijective for finite modules over a Noetherian ring. -/
theorem adicKernelMap_bijective [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N] :
    Function.Bijective (adicKernelMap I f) := by
  refine ⟨fun x y h => AdicCompletion.map_injective I
    (f := f.ker.subtype) Subtype.val_injective (congrArg Subtype.val h), ?_⟩
  intro x
  have he : Function.Exact f.ker.subtype f.rangeRestrict := by
    intro y
    constructor
    · intro hy
      exact ⟨⟨y, congrArg Subtype.val hy⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      exact y.property
  have hx : AdicCompletion.map I f.rangeRestrict x.val = 0 := by
    apply AdicCompletion.map_injective I (f := f.range.subtype) Subtype.val_injective
    rw [map_zero, AdicCompletion.map_comp_apply]
    exact x.property
  have hs : Function.Surjective f.rangeRestrict := by
    intro y
    obtain ⟨z, hz⟩ := y.property
    exact ⟨z, Subtype.ext hz⟩
  obtain ⟨y, hy⟩ :=
    (AdicCompletion.map_exact Subtype.val_injective he hs x.val).mp hx
  exact ⟨y, Subtype.ext hy⟩

/-- The actual linear equivalence comparing completion of the kernel and kernel of completion. -/
def adicKernelEquiv [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N] :
    AdicCompletion I f.ker ≃ₗ[AdicCompletion I R] (AdicCompletion.map I f).ker :=
  LinearEquiv.ofBijective (adicKernelMap I f) (adicKernelMap_bijective I f)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicKernel.Construction
