import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactKernelRecovery
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily

/-! # All Kernel Components -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.AllKernelComponents.IntrinsicChosenRecovery

/-! Recover the one-step active chosen kernel from the complete native
prescription, even when the tested section is specified using a higher
coefficient projector. Both the torsion bound and every separation
equation are derived from the complete kernel and CMPoints coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactKernelRecovery OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {S : Scheme} {d s : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
variable {m n : ℕ} (hmn : m ≤ n)
variable {W P : Over S} [GrpObj W]
variable (pairing : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
  (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels v))
  (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels v)) (W := W))
variable (active : Fin s) (multiplicative : Fin s → Bool)
variable (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P) (hF : F.KilledBy (q ^ m))
variable (hFs : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn F (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels active))

include hmn hF hFs in
theorem active_component_at_higher_projector (T : Over S) (t : T ⟶ P) (a : T ⟶ A.scheme)
    (ha : a ≫ AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ n s labels active = a)
    (hk : a ∈ (Kernel.Models.multiplierFullKernel (q ^ m)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels) pairing active multiplicative F).points T t) :
    a ∈ F.points T t := by
  have hkill := Kernel.Models.multiplierFullKernel_killed (q ^ m)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels) pairing active multiplicative F hF T t a hk
  have hc := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A σ _ _ (q ^ m)
    (by simpa only [Nat.cast_pow] using
      ProjectorLevels.projector_level_congruence j iota hsplit hmn (labels (Sum.inl active))) T a hkill
  have hlow : a ≫ AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels active = a := hc.symm.trans ha
  have hpp : ∀ v w : Fin s, w ≠ v →
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ m) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels w) ≫
        AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ m) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels v) = 1 := by
    intro v w hw
    exact AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45_native_projectors_orthogonal j iota hsplit A σ m
      (labels (Sum.inl w)) (labels (Sum.inl v)) (fun he => hw (Sum.inl.inj (labels.injective he)))
  have hrp : ∀ v w : Fin s,
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ m) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels w) ≫
        AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ m) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels v) = 1 := by
    intro v w
    exact AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45_native_projectors_orthogonal j iota hsplit A σ m
      (labels (Sum.inr w)) (labels (Sum.inl v)) (by
        intro he
        have hc := labels.injective he
        cases hc)
  have h := (CompactKernelRecovery.multiplierFullKernel_chosen_component (q ^ m)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels) pairing active multiplicative F
    hF hFs hpp hrp active T t a hlow).mp hk
  simpa only [Kernel.Base.chosenKernel, ↓reduceIte] using h

include hmn hF hFs in
theorem active_factor_at_higher_projector {H : Over S} [GrpObj H] (i : H ⟶ A.scheme) [IsMonHom i]
    (hFi : F = Kernel.Base.fixedKernelFamily (P := P) i)
    (T : Over S) (t : T ⟶ P) (a : T ⟶ A.scheme)
    (ha : a ≫ AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ n s labels active = a)
    (hk : a ∈ (Kernel.Models.multiplierFullKernel (q ^ m)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels) pairing active multiplicative F).points T t) :
    ∃ h : T ⟶ H, h ≫ i = a := by
  have h := active_component_at_higher_projector j iota hsplit A σ labels hmn pairing active multiplicative
    F hF hFs T t a ha hk
  rw [hFi] at h
  exact h

end AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.AllKernelComponents.IntrinsicChosenRecovery

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.AllKernelComponents

/-! Recover any chosen or opposite component of the native complete
kernel, including when the test section is fixed by a higher-level
coefficient projector. Every separation equation is derived. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactKernelRecovery OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {S : Scheme} {d s : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))

theorem native_label_separation (m : ℕ) (a b : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s) (hab : a ≠ b) :
    AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ m) (σ.map (j.projector iota hsplit m (labels a))) ≫
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ m) (σ.map (j.projector iota hsplit m (labels b))) = 1 :=
  AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45_native_projectors_orthogonal j iota hsplit A σ m (labels a) (labels b)
    (fun h => hab (labels.injective h))

variable {m n : ℕ} (hmn : m ≤ n)
variable {W P : Over S} [GrpObj W]
variable (pairing : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
  (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels v))
  (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels v)) (W := W))
variable (active : Fin s) (multiplicative : Fin s → Bool)
variable (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P) (hF : F.KilledBy (q ^ m))

include hmn hF in
theorem kernel_section_lower_projector (τ : Gal(E/ℚ)) (T : Over S) (t : T ⟶ P) (a : T ⟶ A.scheme)
    (ha : a ≫ σ.map (j.projector iota hsplit n τ) = a)
    (hk : a ∈ (Kernel.Models.multiplierFullKernel (q ^ m)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels) pairing active multiplicative F).points T t) :
    a ≫ σ.map (j.projector iota hsplit m τ) = a := by
  have hkill := Kernel.Models.multiplierFullKernel_killed (q ^ m)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels) pairing active multiplicative F hF T t a hk
  have hc := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A σ _ _ (q ^ m)
    (by simpa only [Nat.cast_pow] using ProjectorLevels.projector_level_congruence j iota hsplit hmn τ) T a hkill
  exact hc.symm.trans ha

variable (hFs : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn F (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels active))

include hmn hF hFs in
theorem chosen_component_higher (v : Fin s) (T : Over S) (t : T ⟶ P) (a : T ⟶ A.scheme)
    (ha : a ≫ AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ n s labels v = a)
    (hk : a ∈ (Kernel.Models.multiplierFullKernel (q ^ m)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels) pairing active multiplicative F).points T t) :
    a ∈ (Kernel.Base.chosenKernel
      (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels w))
      (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels w))
      active multiplicative F v).points T t := by
  have hl := kernel_section_lower_projector j iota hsplit A σ labels hmn pairing active multiplicative F hF
    (labels (.inl v)) T t a ha hk
  apply (CompactKernelRecovery.multiplierFullKernel_chosen_component (q ^ m)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels) pairing active multiplicative F hF hFs
    (fun v w hw => native_label_separation j iota hsplit A σ labels m (.inl w) (.inl v)
      (fun h => hw (Sum.inl.inj h)))
    (fun v w => native_label_separation j iota hsplit A σ labels m (.inr w) (.inl v)
      (by intro h; cases h)) v T t a hl).mp hk

include hmn hF hFs in
theorem opposite_component_higher (v : Fin s) (T : Over S) (t : T ⟶ P) (a : T ⟶ A.scheme)
    (ha : a ≫ AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ n s labels v = a)
    (hk : a ∈ (Kernel.Models.multiplierFullKernel (q ^ m)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels) pairing active multiplicative F).points T t) :
    a ∈ (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel (q ^ m)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels v)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels v) (pairing v)
      (Kernel.Base.chosenKernel
        (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels w))
        (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels w))
        active multiplicative F v)).points T t := by
  have hl := kernel_section_lower_projector j iota hsplit A σ labels hmn pairing active multiplicative F hF
    (labels (.inr v)) T t a ha hk
  apply (CompactKernelRecovery.multiplierFullKernel_opposite_component (q ^ m)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels) pairing active multiplicative F hF hFs
    (fun v w => native_label_separation j iota hsplit A σ labels m (.inl w) (.inr v)
      (by intro h; cases h))
    (fun v w hw => native_label_separation j iota hsplit A σ labels m (.inr w) (.inr v)
      (fun h => hw (Sum.inr.inj h))) v T t a hl).mp hk

end AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.AllKernelComponents

end

end OAI
