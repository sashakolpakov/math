import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedKernelModels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EmbeddedActiveFamilies
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ModeledQuotient
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Stability
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactKernelRecovery

/-! # Integral Canonical Neighbors -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors

/-! Construct the complete integral canonical quotient from an actual
finite flat active q-kernel. All opposite models, torsion and support
bounds, quotient geometry, coefficient action and markings are derived. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ModeledQuotient.Lifts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedKernelModels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EmbeddedActiveFamilies OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Stability

variable {S : Scheme} [IsReduced S] [IsLocallyNoetherian S] {g N s : ℕ} {δ : Fin g → ℕ}
  {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hdegree : q.Coprime (∏ i, δ i))
  (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
  (hlabels : ∀ v : Fin s, labels (.inr v) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (.inl v))
  (n : ℕ) (hn : 1 ≤ n) (active : Fin s) (multiplicative : Fin s → Bool) (P : Over S)
  (H : Kernel.Properties.FiniteFlatKernel (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1)
    (ρ.map (j.projector iota hsplit 1 (labels (.inl active))))))

abbrev integralActiveFamily :=
  EmbeddedActiveFamilies.embeddedActiveFamily (P := P) (q ^ 1) (ρ.map (j.projector iota hsplit 1 (labels (.inl active)))) H

def integralActiveFamilyModel :=
  EmbeddedActiveFamilies.embeddedActiveFamilyModel (P := P) (q ^ 1) (ρ.map (j.projector iota hsplit 1 (labels (.inl active)))) H

include hn in
omit [IsReduced S] [IsLocallyNoetherian S] [NumberField.IsCMField E] in
theorem integralActiveFamily_killed :
    (integralActiveFamily j iota hsplit A ρ labels active P H).KilledBy (q ^ n) :=
  EmbeddedActiveFamilies.embeddedActiveFamily_killed_at_level j iota hsplit A.abelian ρ (labels (.inl active)) H n hn

include hn in
omit [IsReduced S] [IsLocallyNoetherian S] [NumberField.IsCMField E] in
theorem integralActiveFamily_supported :
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (integralActiveFamily j iota hsplit A ρ labels active P H)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels active) :=
  EmbeddedActiveFamilies.embeddedActiveFamily_supported_at_level j iota hsplit A.abelian ρ (labels (.inl active)) H n hn

abbrev integralCanonicalFullKernel :=
  Kernel.Models.multiplierFullKernel (q ^ n)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A.abelian ρ n s labels)
    (ReducedKernelModels.reducedNativeBlockPairings j iota hsplit A ρ labels n) active multiplicative
    (integralActiveFamily j iota hsplit A ρ labels active P H)

def integralCanonicalFullKernelModel :=
  ReducedKernelModels.reducedNativeFullKernelModel j iota hsplit A ρ hρ hdegree labels hlabels n active multiplicative
    (integralActiveFamily j iota hsplit A ρ labels active P H)
    (integralActiveFamilyModel j iota hsplit A ρ labels active P H)
    (integralActiveFamily_killed j iota hsplit A ρ labels n hn active P H)
    (integralActiveFamily_supported j iota hsplit A ρ labels n hn active P H)

include hn in
omit [NumberField.IsCMField E] in
theorem integralCanonicalFullKernel_killed :
    (integralCanonicalFullKernel j iota hsplit A ρ labels n active multiplicative P H).KilledBy (q ^ n) :=
  Kernel.Models.multiplierFullKernel_killed (q ^ n) _ _ _ active multiplicative _
    (integralActiveFamily_killed j iota hsplit A ρ labels n hn active P H)

def integralCanonicalQuotient :=
  Intrinsic.ModeledQuotient.Lifts.constructNativeModeledQuotient A.abelian P
    (integralCanonicalFullKernel j iota hsplit A ρ labels n active multiplicative P H)
    (integralCanonicalFullKernelModel j iota hsplit A ρ hρ hdegree labels hlabels n hn active multiplicative P H)
    (q ^ n) (integralCanonicalFullKernel_killed j iota hsplit A ρ labels n hn active multiplicative P H)

include hn in
omit [NumberField.IsCMField E] in
theorem integralCanonicalFullKernel_stable (a : NumberField.RingOfIntegers E) :
    AbelianScheme.IsogenyQuotient.Action.Construction.RelativeSubgroupStable
      (integralCanonicalFullKernel j iota hsplit A ρ labels n active multiplicative P H) (ρ.map a) :=
  Kernel.Stability.multiplierFullKernel_stable (q ^ n) _ _ _ active multiplicative _
    (integralActiveFamily_killed j iota hsplit A ρ labels n hn active P H)
    (integralActiveFamily_supported j iota hsplit A ρ labels n hn active P H) (ρ.map a)
    (fun v => ((j.residueCharacter iota (labels (.inl v)) n a).val : ℤ))
    (fun v => ((j.residueCharacter iota (labels (.inr v)) n a).val : ℤ))
    (fun v => AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45_native_projector_scalar j iota hsplit A.abelian ρ n (labels (.inl v)) a)
    (fun v => AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45_native_projector_scalar j iota hsplit A.abelian ρ n (labels (.inr v)) a)

def integralCanonicalQuotientAction :=
  (integralCanonicalQuotient j iota hsplit A ρ hρ hdegree labels hlabels n hn active multiplicative P H).action ρ
    (integralCanonicalFullKernel_stable j iota hsplit A ρ labels n hn active multiplicative P H)

def integralCanonicalQuotientLevel (hcop : q.Coprime N) :=
  (integralCanonicalQuotient j iota hsplit A ρ hρ hdegree labels hlabels n hn active multiplicative P H).level N
    (hcop.pow_left n) (A.pullback P.hom).level

end AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors

namespace AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors.ChosenKernelCriterion

/-! Recover each chosen component of the actual integral canonical
kernel. All compact and opposite separation equations follow from the
original coefficient projectors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactKernelRecovery OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedKernelModels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.AllKernelComponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EmbeddedActiveFamilies

variable {S : Scheme.{0}} [IsReduced S] [IsLocallyNoetherian S] {g N s : ℕ} {δ : Fin g → ℕ}
  {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ)) (n : ℕ) (hn : 1 ≤ n) (active : Fin s)
  (multiplicative : Fin s → Bool) (P : Over S)
  (H : Kernel.Properties.FiniteFlatKernel (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1)
    (ρ.map (j.projector iota hsplit 1 (labels (.inl active))))))

include hn in
theorem integralCanonicalFullKernel_chosen_component
    (v : Fin s) (T : Over S) (t : T ⟶ P) (a : T ⟶ A.abelian.scheme)
    (ha : a ≫ AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels v = a) :
    a ∈ (integralCanonicalFullKernel j iota hsplit A ρ labels n active multiplicative P H).points T t ↔
      a ∈ (Kernel.Base.chosenKernel
        (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels w))
        (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels w))
        active multiplicative (integralActiveFamily j iota hsplit A ρ labels active P H) v).points T t :=
  CompactKernelRecovery.multiplierFullKernel_chosen_component (q ^ n)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A.abelian ρ n s labels)
    (ReducedKernelModels.reducedNativeBlockPairings j iota hsplit A ρ labels n) active multiplicative
    (integralActiveFamily j iota hsplit A ρ labels active P H)
    (integralActiveFamily_killed j iota hsplit A ρ labels n hn active P H)
    (integralActiveFamily_supported j iota hsplit A ρ labels n hn active P H)
    (fun v w hw => Intrinsic.AllKernelComponents.native_label_separation j iota hsplit A.abelian ρ labels n (.inl w) (.inl v)
      (fun he => hw (Sum.inl.inj he)))
    (fun v w => Intrinsic.AllKernelComponents.native_label_separation j iota hsplit A.abelian ρ labels n (.inr w) (.inl v)
      (by intro he; cases he)) v T t a ha

include hn in
theorem integralCanonicalFullKernel_active_factor
    (T : Over S) (t : T ⟶ P) (a : T ⟶ A.abelian.scheme)
    (ha : a ≫ AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels active = a) :
    a ∈ (integralCanonicalFullKernel j iota hsplit A ρ labels n active multiplicative P H).points T t ↔
      ∃ u : T ⟶ H.carrier,
        u ≫ (H.inclusion ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1)
          (ρ.map (j.projector iota hsplit 1 (labels (.inl active))))) = a := by
  have h := integralCanonicalFullKernel_chosen_component j iota hsplit A ρ labels n hn
    active multiplicative P H active T t a ha
  simp only [Kernel.Base.chosenKernel, ↓reduceIte] at h
  unfold integralActiveFamily EmbeddedActiveFamilies.embeddedActiveFamily Kernel.Base.fixedKernelFamily EmbeddedActiveFamilies.embeddedActiveMap at h
  exact h

include hn in
theorem integralCanonicalFullKernel_compact_multiplicative
    (v : Fin s) (hv : v ≠ active) (hm : multiplicative v = true)
    (T : Over S) (t : T ⟶ P) (a : T ⟶ A.abelian.scheme)
    (ha : a ≫ AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels v = a) :
    a ∈ (integralCanonicalFullKernel j iota hsplit A ρ labels n active multiplicative P H).points T t ↔
      a ^ (q ^ n) = 1 := by
  rw [integralCanonicalFullKernel_chosen_component j iota hsplit A ρ labels n hn
    active multiplicative P H v T t a ha]
  simp only [Kernel.Base.chosenKernel, ite_eq_right hv, hm, ↓reduceIte]
  constructor
  · rintro ⟨u, rfl⟩
    change (u ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels v)) ^ (q ^ n) = 1
    rw [← MonObj.comp_pow, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.comp_one]
  · intro h
    exact ⟨AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift (q ^ n) _ a h ha, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift_inclusion _ _ _ _ _⟩

include hn in
theorem integralCanonicalFullKernel_compact_etale
    (v : Fin s) (hv : v ≠ active) (he : multiplicative v = false)
    (T : Over S) (t : T ⟶ P) (a : T ⟶ A.abelian.scheme)
    (ha : a ≫ AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels v = a) :
    a ∈ (integralCanonicalFullKernel j iota hsplit A ρ labels n active multiplicative P H).points T t ↔
      a = 1 := by
  rw [integralCanonicalFullKernel_chosen_component j iota hsplit A ρ labels n hn
    active multiplicative P H v T t a ha]
  simp only [Kernel.Base.chosenKernel, ite_eq_right hv, he, Bool.false_eq_true, ↓reduceIte]
  rfl

end AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors.ChosenKernelCriterion

end

end OAI
