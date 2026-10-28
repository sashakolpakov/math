import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineKernelData
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.UniversalParameterKernels

/-! # Fine Classification -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineClassification

noncomputable section

/-! The native representing family and its proved universal chosen kernels
give IsogenyQuotient classification on every test of the original fine moduli model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] [Field L] [NumberField L] {κ : L →+* ℂ}
  {q s N : ℕ} [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (arithmeticEmbedding : E →+* L)
  (hsplit : j.HasSplitCoordinates arithmeticEmbedding)
  (labels : Fin s → Gal(E/ℚ)) (t : AbelianScheme.TateComparison.Local.IntegralType s)
  [∀ v, Module (ZMod (q ^ t.multiplierNat)) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (t.exponentNat v))]
  (Q : Over M.space.left)
  (repr : (ParameterKernels.nativeKernelFunctor j arithmeticEmbedding hsplit M.space (FineKernelData.fineFamily M)
    t.multiplierNat labels t.exponentNat).RepresentableBy Q)
  (dst : AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter M.space Q ⟶ M.space)
  (hQf : IsFinite Q.hom) (hQe : Etale Q.hom)

abbrev parameterCorrespondence : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space where
  cover := AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter M.space Q
  source := AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q
  target := dst
  finite := hQf
  etale := hQe

theorem represented_isogeny_classifies
    (f : FineKernelData.UniversalIsogeny (q := q) M (parameterCorrespondence M Q dst hQf hQe) t)
    (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])
    (hχ : ∀ v, χ (v, false) = j.localCharacter arithmeticEmbedding (labels v))
    (hkernel : ∀ v, FineKernelData.chosenKernel M (parameterCorrespondence M Q dst hQf hQe) t χ f v =
      (UniversalParameterKernels.representedKernels j arithmeticEmbedding hsplit M.space (FineKernelData.fineFamily M)
        t.multiplierNat labels t.exponentNat Q repr).val v) :
    FineKernelData.ClassifiesChosenKernels M (parameterCorrespondence M Q dst hQf hQe) t χ f := by
  refine ⟨?_, ?_⟩
  · intro v
    rw [hkernel v]
    exact ⟨(UniversalParameterKernels.representedKernels j arithmeticEmbedding hsplit M.space (FineKernelData.fineFamily M)
      t.multiplierNat labels t.exponentNat Q repr).property v |>.1,
      (UniversalParameterKernels.representedKernels j arithmeticEmbedding hsplit M.space (FineKernelData.fineFamily M)
        t.multiplierNat labels t.exponentNat Q repr).property v |>.2.2⟩
  · intro T x H
    let H' : AbelianScheme.TateComparison.Subgroups.KernelChoices ((FineKernelData.fineFamily M).pullback x.left)
        (fun v => j.localCharacter arithmeticEmbedding (labels v)) t.multiplierNat t.exponentNat :=
      ⟨H.val, fun v => by
        refine ⟨(H.property v).1, ?_, (H.property v).2.2⟩
        intro U z hz
        exact (congrArg (fun ψ => z ∈ (AbelianScheme.TateComparison.Subgroups.splitBlock ((FineKernelData.fineFamily M).pullback x.left)
          ψ t.multiplierNat).atTest U) (hχ v)).mp ((H.property v).2.1 U hz)⟩
    let e := ParameterKernels.parameterFiberKernelEquiv j arithmeticEmbedding hsplit M.space (FineKernelData.fineFamily M)
      t.multiplierNat labels t.exponentNat Q repr T x
    let c := e.symm H'
    have branch (b : AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.SourceFiber (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q) x) (v : Fin s) :
        FineKernelData.chosenKernelAtLift M (parameterCorrespondence M Q dst hQf hQe) t χ f x b.val b.property v =
          (e b).val v := by
      unfold FineKernelData.chosenKernelAtLift
      rw [hkernel]
      exact UniversalParameterKernels.representedKernels_at_branch j arithmeticEmbedding hsplit M.space (FineKernelData.fineFamily M)
        t.multiplierNat labels t.exponentNat Q repr T x b v
    have hval (v : Fin s) : (e c).val v = H.val v := by
      have hv := congrArg (fun H => H.val v) (e.apply_symm_apply H')
      exact hv
    refine ⟨c.val, ⟨c.property, fun v => (branch c v).trans (hval v)⟩, ?_⟩
    rintro b ⟨hb, hk⟩
    have he : e ⟨b, hb⟩ = e c := by
      apply Subtype.ext
      funext v
      exact (branch ⟨b, hb⟩ v).symm.trans ((hk v).trans (hval v).symm)
    exact congrArg Subtype.val (e.injective he)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineClassification
