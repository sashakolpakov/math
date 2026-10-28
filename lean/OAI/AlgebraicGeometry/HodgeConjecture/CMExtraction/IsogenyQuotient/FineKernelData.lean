import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotient
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELFamily

/-! # Fine Kernel Data -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineKernelData

noncomputable section

/-! Actual fine-model families and the chosen-kernel classification component
of IsogenyQuotient. The complete input will retain the quotient geometry, full kernel,
polarization and marking comparisons, and raw-Hecke multiset identity for
the same correspondence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s N q : ℕ} [Fact q.Prime]
  {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)

abbrev fineFamily : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N M.space.left :=
  HeckeCycles.PELFamily.CM.Family.ofActionData (PELModuli.IntegralModel.PEL.Has.characteristicZeroPELData P M.universal)

variable (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space) (t : AbelianScheme.TateComparison.Local.IntegralType s)
  (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])

abbrev sourceFamily := (fineFamily M).pullback C.source.left
abbrev targetFamily := (fineFamily M).pullback C.target.left

abbrev UniversalIsogeny :=
  AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (sourceFamily M C) (targetFamily M C) (q ^ t.multiplierNat)

def chosenKernel (f : UniversalIsogeny (q := q) M C t) (v : Fin s) :
    AbelianScheme.TateComparison.Subgroups.PointSubgroup (sourceFamily M C).abelian :=
  (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel f.isogeny.hom).inf
    (AbelianScheme.TateComparison.Subgroups.splitBlock (sourceFamily M C) (χ (v, false)) t.multiplierNat)

abbrev chosenKernels {T : Over (Spec (.of K))} (x : T ⟶ M.space) :=
  AbelianScheme.TateComparison.Subgroups.KernelChoices ((fineFamily M).pullback x.left) (fun v => χ (v, false))
    t.multiplierNat t.exponentNat

def chosenKernelAtLift (f : UniversalIsogeny (q := q) M C t)
    {T : Over (Spec (.of K))} (x : T ⟶ M.space)
    (c : T ⟶ C.cover) (w : c ≫ C.source = x) (v : Fin s) :
    AbelianScheme.TateComparison.Subgroups.PointSubgroup ((fineFamily M).pullback x.left).abelian :=
  ((chosenKernel M C t χ f v).pullback c.left).comapHom
    (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso (fineFamily M).abelian c.left C.source.left x.left
      (congrArg (fun z => z.left) w)).hom

def ClassifiesChosenKernels (f : UniversalIsogeny (q := q) M C t) : Prop :=
  (∀ v, (chosenKernel M C t χ f v).HasFiniteEtaleModel ∧
    (chosenKernel M C t χ f v).HasGeometricType q (t.exponentNat v)) ∧
  ∀ (T : Over (Spec (.of K))) (x : T ⟶ M.space)
    (F : chosenKernels M t χ x),
    ∃! c : T ⟶ C.cover, ∃ w : c ≫ C.source = x,
      ∀ v, chosenKernelAtLift M C t χ f x c w v = F.val v

theorem classified_kernel_lift (f : UniversalIsogeny (q := q) M C t)
    (hf : ClassifiesChosenKernels M C t χ f)
    (T : Over (Spec (.of K))) (x : T ⟶ M.space) (F : chosenKernels M t χ x) :
    ∃! c : T ⟶ C.cover, ∃ w : c ≫ C.source = x,
      ∀ v, chosenKernelAtLift M C t χ f x c w v = F.val v :=
  hf.2 T x F

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineKernelData
