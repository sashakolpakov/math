import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Fiber Flat Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberFlatCriterion.LocalSectionLifting

noncomputable section

/-! Lifting finite-module isomorphisms from the residue-field fiber in Openness. -/

open IsLocalRing TensorProduct
open scoped TensorProduct

variable (R A : Type*) [CommRing R] [CommRing A]
  [IsLocalRing R] [IsLocalRing A] [Algebra R A]
  [IsLocalHom (algebraMap R A)]

/-- Nakayama over a local algebra detects a finite module using the residue
field of the smaller local ring. -/
theorem subsingleton_of_residueField_tensor
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] [Module.Finite A M]
    [Subsingleton (ResidueField R ⊗[R] M)] : Subsingleton M := by
  have : Subsingleton
      (ResidueField A ⊗[ResidueField R] (ResidueField R ⊗[R] M)) := inferInstance
  have : Subsingleton (ResidueField A ⊗[R] M) :=
    (AlgebraTensorModule.cancelBaseChange R (ResidueField R) (ResidueField A)
      (ResidueField A) M).surjective.subsingleton
  have : Subsingleton (ResidueField A ⊗[A] M) :=
    (TensorProduct.mapOfCompatibleSMul_surjective A R (ResidueField A) (ResidueField A) M).subsingleton
  exact (IsLocalRing.subsingleton_tensorProduct (R := A) (M := M)).mp inferInstance

variable {R A}

/-- Surjectivity of a finite-module map over a local algebra can be checked
after base change to the residue field of the base ring. -/
theorem surjective_of_residueField_tensor
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module A M] [IsScalarTower R A M]
    [Module R N] [Module A N] [IsScalarTower R A N] [Module.Finite A N]
    (f : M →ₗ[A] N)
    (hf : Function.Surjective ((f.restrictScalars R).lTensor (ResidueField R))) :
    Function.Surjective f := by
  let Q := N ⧸ LinearMap.range f
  let g : N →ₗ[A] Q := (LinearMap.range f).mkQ
  have hg : Function.Surjective (g.restrictScalars R) :=
    Submodule.mkQ_surjective (LinearMap.range f)
  have hex : Function.Exact (f.restrictScalars R) (g.restrictScalars R) :=
    f.exact_map_mkQ_range
  have htex := _root_.lTensor_exact (ResidueField R) hex hg
  have hgtex := (g.restrictScalars R).lTensor_surjective (ResidueField R) hg
  have : Subsingleton (ResidueField R ⊗[R] Q) := by
    refine (subsingleton_iff_forall_eq 0).mpr fun q => ?_
    obtain ⟨n, rfl⟩ := hgtex q
    obtain ⟨m, rfl⟩ := hf n
    exact htex.apply_apply_eq_zero m
  have : Subsingleton Q := subsingleton_of_residueField_tensor R A Q
  intro n
  have hn : g n = 0 := Subsingleton.elim _ _
  have hnk : n ∈ LinearMap.ker ((LinearMap.range f).mkQ) := hn
  change n ∈ LinearMap.range f
  simpa only [Submodule.ker_mkQ] using hnk

/-- For a surjection with flat codomain over the base, injectivity on its
residue-field fiber lifts to injectivity over the local algebra. -/
theorem injective_of_surjective_of_flat_of_residueField_tensor
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module A M] [IsScalarTower R A M]
    [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.Finite A M] [Module.FinitePresentation A N] [Module.Flat R N]
    (f : M →ₗ[A] N) (hsurj : Function.Surjective f)
    (hinj : Function.Injective ((f.restrictScalars R).lTensor (ResidueField R))) :
    Function.Injective f := by
  let H := LinearMap.ker f
  have : Module.Finite A H := .of_fg (Module.FinitePresentation.fg_ker f hsurj)
  let i : H →ₗ[A] M := H.subtype
  have hi : Function.Injective (i.restrictScalars R) := Subtype.val_injective
  have hex : Function.Exact (i.restrictScalars R) (f.restrictScalars R) :=
    f.exact_subtype_ker_map
  have hit := LinearMap.lTensor_injective_of_exact_of_flat
    (f.restrictScalars R) hsurj (i.restrictScalars R) hi hex (ResidueField R)
  have htex := _root_.lTensor_exact (ResidueField R) hex hsurj
  have : Subsingleton (ResidueField R ⊗[R] H) := by
    refine (subsingleton_iff_forall_eq 0).mpr fun h => ?_
    apply hit
    apply hinj
    simpa only [map_zero] using htex.apply_apply_eq_zero h
  have : Subsingleton H := subsingleton_of_residueField_tensor R A H
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.subsingleton_iff_eq_bot.mp inferInstance

/-- A map of finite modules with flat codomain over the local base is an
isomorphism if its base residue-field fiber is an isomorphism. -/
theorem bijective_of_flat_of_residueField_tensor
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module A M] [IsScalarTower R A M]
    [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.Finite A M] [Module.FinitePresentation A N] [Module.Flat R N]
    (f : M →ₗ[A] N)
    (hf : Function.Bijective ((f.restrictScalars R).lTensor (ResidueField R))) :
    Function.Bijective f := by
  have hs := surjective_of_residueField_tensor f hf.surjective
  exact ⟨injective_of_surjective_of_flat_of_residueField_tensor f hs hf.injective, hs⟩

/-- A finite flat module mapping to a base-flat, finitely presented module
by a residue-field isomorphism certifies flatness over the local algebra. -/
theorem flat_of_flat_source_of_residueField_tensor_iso
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module A M] [IsScalarTower R A M]
    [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.Finite A M] [Module.Flat A M]
    [Module.FinitePresentation A N] [Module.Flat R N]
    (f : M →ₗ[A] N)
    (hf : Function.Bijective ((f.restrictScalars R).lTensor (ResidueField R))) :
    Module.Flat A N := by
  let e : M ≃ₗ[A] N := LinearEquiv.ofBijective f
    (bijective_of_flat_of_residueField_tensor f hf)
  exact Module.Flat.of_linearEquiv e.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberFlatCriterion.LocalSectionLifting
