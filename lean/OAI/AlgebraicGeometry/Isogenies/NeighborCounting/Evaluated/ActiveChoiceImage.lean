import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveChoiceTorsion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrimeProjectorSupport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OppositeKernel

/-! # Active Choice Image -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage.Prime

/-! The original evaluated active choice itself has a finite flat model
inside the literal prime-level block. Its lower torsion and support
conditions are derived from the original module type and projectors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OppositeKernel.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveChoiceTorsion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrimeProjectorSupport

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {L : Type} [Field L] [CharZero L] {g s : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of L)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (c : Fin s → Bool) (p : Fin 3 → Fin (s + 1) → (A.scheme ⟶ A.scheme))
  [∀ i v, IsMonHom (p i v)] (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)
  (d : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L (Intrinsic.HeckeEvaluation.neighborEvaluationSchemes A q 0 (Fin.cases false c) p hTorsionQuotient))
  (i : Fin 3) (τ : Gal(E/ℚ))
  (hp : p i 0 = ρ.map (j.projector iota hsplit (HeckeExponents.neighborLevel i) τ))

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (v : Fin (s + 1)) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i)
    (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false c) i v)

variable (a : ULift (Fin (d.count (some i))))

def evaluatedPrimeActiveChoice :=
  Reference.ParameterSubspaces.evaluatedTuple q c i (p i) (Intrinsic.ChoiceFunctor.nativeChoiceRepresentation A q c p hTorsionQuotient i) (d.family (some i)) a 0

theorem evaluatedPrimeActiveChoice_killed :
    (evaluatedPrimeActiveChoice A c p hTorsionQuotient d i a).val.subgroup.KilledBy q :=
  ActiveChoiceTorsion.activeChoice_killed A q 0 (Fin.cases false c) i
    (evaluatedPrimeActiveChoice A c p hTorsionQuotient d i a).val hTorsionQuotient

include hp in
theorem evaluatedPrimeActiveChoice_supported :
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (evaluatedPrimeActiveChoice A c p hTorsionQuotient d i a).val.subgroup
      (ρ.map (j.projector iota hsplit 1 τ)) := by
  apply PrimeProjectorSupport.prime_projector_supported j iota hsplit A ρ _ (HeckeExponents.neighborLevel i)
    (Nat.succ_le_succ (Nat.zero_le i.val)) τ
    (evaluatedPrimeActiveChoice_killed A c p hTorsionQuotient d i a)
  rw [← hp]
  exact (evaluatedPrimeActiveChoice A c p hTorsionQuotient d i a).property

def evaluatedPrimeActiveSubgroup :=
  AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q (ρ.map (j.projector iota hsplit 1 τ)))
    (evaluatedPrimeActiveChoice A c p hTorsionQuotient d i a).val.subgroup

def evaluatedPrimeActiveSubgroupModel :
    (evaluatedPrimeActiveSubgroup j iota hsplit A ρ c p hTorsionQuotient d i τ a).Model :=
  AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.supportedTorsionBlock_model q (ρ.map (j.projector iota hsplit 1 τ))
    (evaluatedPrimeActiveChoice A c p hTorsionQuotient d i a).val.subgroup
    (Classical.choice (evaluatedPrimeActiveChoice A c p hTorsionQuotient d i a).val.geometric)
    (evaluatedPrimeActiveChoice_killed A c p hTorsionQuotient d i a)
    (evaluatedPrimeActiveChoice_supported j iota hsplit A ρ c p hTorsionQuotient d i τ hp a)

end AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage.Prime

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage

/-! The modeled prime block subgroup embeds as the unchanged original active choice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OppositeKernel.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveChoiceTorsion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrimeProjectorSupport OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage.Prime

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {L : Type} [Field L] [CharZero L] {g s : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of L)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (c : Fin s → Bool) (p : Fin 3 → Fin (s + 1) → (A.scheme ⟶ A.scheme))
  [∀ i v, IsMonHom (p i v)] (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)
  (d : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L (Intrinsic.HeckeEvaluation.neighborEvaluationSchemes A q 0 (Fin.cases false c) p hTorsionQuotient))
  (i : Fin 3) (τ : Gal(E/ℚ))
  (hp : p i 0 = ρ.map (j.projector iota hsplit (HeckeExponents.neighborLevel i) τ))

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (v : Fin (s + 1)) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i)
    (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false c) i v)

variable (a : ULift (Fin (d.count (some i))))

include hp in
theorem evaluatedPrimeActiveSubgroup_image :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q (ρ.map (j.projector iota hsplit 1 τ)))
      (ActiveChoiceImage.Prime.evaluatedPrimeActiveSubgroup j iota hsplit A ρ c p hTorsionQuotient d i τ a) =
    (ActiveChoiceImage.Prime.evaluatedPrimeActiveChoice A c p hTorsionQuotient d i a).val.subgroup :=
  AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.supportedTorsionBlock_image q (ρ.map (j.projector iota hsplit 1 τ))
    (ActiveChoiceImage.Prime.evaluatedPrimeActiveChoice A c p hTorsionQuotient d i a).val.subgroup
    (ActiveChoiceImage.Prime.evaluatedPrimeActiveChoice_killed A c p hTorsionQuotient d i a)
    (ActiveChoiceImage.Prime.evaluatedPrimeActiveChoice_supported j iota hsplit A ρ c p hTorsionQuotient d i τ hp a)

end AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage

end

end OAI
