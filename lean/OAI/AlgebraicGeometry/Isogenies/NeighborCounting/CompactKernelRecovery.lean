import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Projection

/-! # Compact Kernel Recovery -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactKernelRecovery

noncomputable section

/-!
Recover the literal q^i-torsion compact chosen kernels from the full
chosen/opposite prescription. Orthogonality of the actual torsion
projectors supplies every separation used in the extraction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]
variable (n : ℕ) {s : ℕ} (p r : Fin s → (A ⟶ A))
variable [∀ v, IsMonHom (p v)] [∀ v, IsMonHom (r v)]
variable {W : Over S} [GrpObj W]
variable (pairing : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
  (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (p v)) (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (r v)) (W := W))
variable (active : Fin s) (multiplicative : Fin s → Bool)
variable (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
variable (hkilled : F.KilledBy n) (hsupport : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn F (p active))
variable (hpp : ∀ v w, w ≠ v → AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (p w) ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (p v) = 1)
variable (hrp : ∀ v w, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (r w) ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (p v) = 1)

include hkilled hsupport hpp hrp in
/-- Restriction of the complete kernel to a chosen block recovers its
specified chosen subgroup, with all opposite and other-place contributions
eliminated by the native torsion-projector equations. -/
theorem multiplierFullKernel_chosen_component
    (v : Fin s) (T : Over S) (t : T ⟶ P) (a : T ⟶ A) (ha : a ≫ p v = a) :
    a ∈ (Kernel.Models.multiplierFullKernel n p r pairing active multiplicative F).points T t ↔
      a ∈ (Kernel.Base.chosenKernel (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (p w))
        (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (p w)) active multiplicative F v).points T t := by
  let C := Kernel.Base.chosenKernel (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (p w))
    (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (p w)) active multiplicative F
  let O := fun v => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n (p v) (r v) (pairing v) (C v)
  have hCkill (v : Fin s) : (C v).KilledBy n :=
    Kernel.Models.multiplier_chosenKernel_killed n p active multiplicative F hkilled v
  have hCsupp (v : Fin s) : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (C v) (p v) :=
    Kernel.Models.multiplier_chosenKernel_supported n p active multiplicative F hsupport v
  have hOann (v w : Fin s) : AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy (O w) (p v) :=
    Kernel.Models.supported_kernel_annihilated n (p v) (r w) (O w)
      (Kernel.Models.oppositeKernel_killed n (p w) (r w) (pairing w) (C w))
      (Kernel.Models.oppositeKernel_supported n (p w) (r w) (pairing w) (C w)) (hrp v w)
  exact Kernel.Projection.chosen_component_of_full_tuple s C O v (p v) (hCsupp v) (hOann v v)
    (fun w hw U u x hx => by
      have hCann : AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy (C w) (p v) :=
        Kernel.Models.supported_kernel_annihilated n (p v) (p w) (C w) (hCkill w) (hCsupp w) (hpp v w hw)
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      rw [MonObj.mul_comp, hCann U u y hy, hOann v w U u z hz, one_mul]) T t a ha

include hkilled hsupport hpp hrp in
/-- A compact multiplicative chosen block contributes exactly its full
n-torsion, where n is the actual multiplier q^i. -/
theorem multiplierFullKernel_compact_multiplicative
    (v : Fin s) (hv : v ≠ active) (hmul : multiplicative v = true)
    (T : Over S) (t : T ⟶ P) (a : T ⟶ A) (ha : a ≫ p v = a) :
    a ∈ (Kernel.Models.multiplierFullKernel n p r pairing active multiplicative F).points T t ↔ a ^ n = 1 := by
  classical
  rw [multiplierFullKernel_chosen_component n p r pairing active multiplicative F
    hkilled hsupport hpp hrp v T t a ha]
  simp only [Kernel.Base.chosenKernel, ite_eq_right hv, hmul, ↓reduceIte]
  constructor
  · rintro ⟨x, rfl⟩
    change (x ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (p v)) ^ n = 1
    rw [← MonObj.comp_pow, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.comp_one]
  · intro h
    exact ⟨AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift n (p v) a h ha, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift_inclusion _ _ _ _ _⟩

include hkilled hsupport hpp hrp in
/-- A compact etale chosen block contributes the trivial subgroup, again
as a statement on all test schemes. -/
theorem multiplierFullKernel_compact_etale
    (v : Fin s) (hv : v ≠ active) (het : multiplicative v = false)
    (T : Over S) (t : T ⟶ P) (a : T ⟶ A) (ha : a ≫ p v = a) :
    a ∈ (Kernel.Models.multiplierFullKernel n p r pairing active multiplicative F).points T t ↔ a = 1 := by
  classical
  rw [multiplierFullKernel_chosen_component n p r pairing active multiplicative F
    hkilled hsupport hpp hrp v T t a ha]
  simp only [Kernel.Base.chosenKernel, ite_eq_right hv, het, Bool.false_eq_true, ↓reduceIte]
  rfl

include hkilled hsupport in
/-- Recovery of the opposite component uses the opposite projector and
derives separation from every chosen and other opposite block. -/
theorem multiplierFullKernel_opposite_component
    (hpr : ∀ v w, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (p w) ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (r v) = 1)
    (hrr : ∀ v w, w ≠ v → AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (r w) ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (r v) = 1)
    (v : Fin s) (T : Over S) (t : T ⟶ P) (a : T ⟶ A) (ha : a ≫ r v = a) :
    a ∈ (Kernel.Models.multiplierFullKernel n p r pairing active multiplicative F).points T t ↔
      a ∈ (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n (p v) (r v) (pairing v)
        (Kernel.Base.chosenKernel (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (p w))
          (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (p w)) active multiplicative F v)).points T t := by
  let C := Kernel.Base.chosenKernel (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (p w))
    (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (p w)) active multiplicative F
  let O := fun v => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n (p v) (r v) (pairing v) (C v)
  have hCkill (v : Fin s) : (C v).KilledBy n :=
    Kernel.Models.multiplier_chosenKernel_killed n p active multiplicative F hkilled v
  have hCsupp (v : Fin s) : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (C v) (p v) :=
    Kernel.Models.multiplier_chosenKernel_supported n p active multiplicative F hsupport v
  have hCann (v w : Fin s) : AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy (C w) (r v) :=
    Kernel.Models.supported_kernel_annihilated n (r v) (p w) (C w) (hCkill w) (hCsupp w) (hpr v w)
  have hOsupp (v : Fin s) : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (O v) (r v) :=
    Kernel.Models.oppositeKernel_supported n (p v) (r v) (pairing v) (C v)
  exact Kernel.Projection.opposite_component_of_full_tuple s C O v (r v) (hOsupp v) (hCann v v)
    (fun w hw U u x hx => by
      have hOann : AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy (O w) (r v) :=
        Kernel.Models.supported_kernel_annihilated n (r v) (r w) (O w)
          (Kernel.Models.oppositeKernel_killed n (p w) (r w) (pairing w) (C w)) (hOsupp w) (hrr v w hw)
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      rw [MonObj.mul_comp, hCann v w U u y hy, hOann U u z hz, one_mul]) T t a ha

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactKernelRecovery
