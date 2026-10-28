import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.AllKernelComponents
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Containment
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactOpposites

/-! # Compact Kernel Components -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CompactKernelComponents

noncomputable section

/-! Exact compact restrictions of a complete native kernel under any
higher coefficient projector. The nonzero restrictions retain the
literal lower multiplier q^m, including on nonreduced test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactOpposites.Kernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.AllKernelComponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Containment

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

include hmn in
theorem lower_projector_of_killed (τ : Gal(E/ℚ)) (T : Over S) (a : T ⟶ A.scheme)
    (ha : a ≫ σ.map (j.projector iota hsplit n τ) = a) (hk : a ^ (q ^ m) = 1) :
    a ≫ σ.map (j.projector iota hsplit m τ) = a := by
  have hc := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A σ _ _ (q ^ m)
    (by simpa only [Nat.cast_pow] using ProjectorLevels.projector_level_congruence j iota hsplit hmn τ) T a hk
  exact hc.symm.trans ha

include hmn hF hFs in
theorem compact_chosen_higher (v : Fin s) (hv : v ≠ active)
    (T : Over S) (t : T ⟶ P) (a : T ⟶ A.scheme)
    (ha : a ≫ AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ n s labels v = a) :
    a ∈ (Kernel.Models.multiplierFullKernel (q ^ m)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels) pairing active multiplicative F).points T t ↔
      if multiplicative v then a ^ (q ^ m) = 1 else a = 1 := by
  classical
  constructor
  · intro hk
    have hc := AllKernelComponents.chosen_component_higher j iota hsplit A σ labels hmn pairing active multiplicative
      F hF hFs v T t a ha hk
    cases hb : multiplicative v
    · simp only [Kernel.Base.chosenKernel, ite_eq_right hv, hb, Bool.false_eq_true, ↓reduceIte] at hc
      change a = 1 at hc
      exact hc
    · simp only [↓reduceIte]
      exact Kernel.Models.multiplierFullKernel_killed _ _ _ pairing active multiplicative F hF T t a hk
  · intro hk
    apply Kernel.Containment.full_kernel_contains_chosen _ _ _ pairing active multiplicative F v T t a
    cases hb : multiplicative v
    · simp only [Kernel.Base.chosenKernel, ite_eq_right hv, hb, Bool.false_eq_true, ↓reduceIte]
      change a = 1
      simpa only [hb, Bool.false_eq_true, ↓reduceIte] using hk
    · simp only [hb, ↓reduceIte] at hk
      simp only [Kernel.Base.chosenKernel, ite_eq_right hv, hb, ↓reduceIte]
      exact ⟨AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift (q ^ m) _ a hk
        (lower_projector_of_killed j iota hsplit A σ hmn (labels (.inl v)) T a ha hk),
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift_inclusion _ _ _ _ _⟩

include hmn hF hFs in
theorem compact_opposite_higher (v : Fin s) (hv : v ≠ active)
    (hCartierDuality : (pairing v).relativeAnnihilator
      ((pairing v).flip.relativeAnnihilator
        (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m)
          (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels v)) (P := P))) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m)
        (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels v)) (P := P))
    (T : Over S) (t : T ⟶ P) (a : T ⟶ A.scheme)
    (ha : a ≫ AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ n s labels v = a) :
    a ∈ (Kernel.Models.multiplierFullKernel (q ^ m)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ m s labels)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ m s labels) pairing active multiplicative F).points T t ↔
      if multiplicative v then a = 1 else a ^ (q ^ m) = 1 := by
  classical
  constructor
  · intro hk
    have hc := AllKernelComponents.opposite_component_higher j iota hsplit A σ labels hmn pairing active multiplicative
      F hF hFs v T t a ha hk
    cases hb : multiplicative v
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact Kernel.Models.multiplierFullKernel_killed _ _ _ pairing active multiplicative F hF T t a hk
    · simp only [Kernel.Base.chosenKernel, ite_eq_right hv, hb, ↓reduceIte] at hc
      rw [CompactOpposites.Kernel.opposite_of_whole _ _ _ _ hCartierDuality] at hc
      change a = 1 at hc
      exact hc
  · intro hk
    apply Kernel.Containment.full_kernel_contains_opposite _ _ _ pairing active multiplicative F v T t a
    cases hb : multiplicative v
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hk
      simp only [Kernel.Base.chosenKernel, ite_eq_right hv, hb, Bool.false_eq_true, ↓reduceIte]
      rw [CompactOpposites.Kernel.opposite_of_trivial]
      exact ⟨AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift (q ^ m) _ a hk
        (lower_projector_of_killed j iota hsplit A σ hmn (labels (.inr v)) T a ha hk),
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift_inclusion _ _ _ _ _⟩
    · simp only [Kernel.Base.chosenKernel, ite_eq_right hv, hb, ↓reduceIte]
      rw [CompactOpposites.Kernel.opposite_of_whole _ _ _ _ hCartierDuality]
      change a = 1
      simpa only [hb, ↓reduceIte] using hk

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CompactKernelComponents
