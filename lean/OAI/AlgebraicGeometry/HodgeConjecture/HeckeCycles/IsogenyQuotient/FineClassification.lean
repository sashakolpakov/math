import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineKernelData
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.UniversalParameterKernels

/-! # Fine Classification -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.FineClassification.CM

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
  (repr : (CMExtraction.IsogenyQuotient.ParameterKernels.nativeKernelFunctor j arithmeticEmbedding hsplit M.space (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M)
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
    (f : CMExtraction.IsogenyQuotient.FineKernelData.UniversalIsogeny (q := q) M (parameterCorrespondence M Q dst hQf hQe) t)
    (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])
    (hχ : ∀ v, χ (v, false) = j.localCharacter arithmeticEmbedding (labels v))
    (hkernel : ∀ v, CMExtraction.IsogenyQuotient.FineKernelData.chosenKernel M (parameterCorrespondence M Q dst hQf hQe) t χ f v =
      (CMExtraction.IsogenyQuotient.UniversalParameterKernels.representedKernels j arithmeticEmbedding hsplit M.space (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M)
        t.multiplierNat labels t.exponentNat Q repr).val v) :
    CMExtraction.IsogenyQuotient.FineKernelData.ClassifiesChosenKernels M (parameterCorrespondence M Q dst hQf hQe) t χ f := by
  refine ⟨?_, ?_⟩
  · intro v
    rw [hkernel v]
    exact ⟨(CMExtraction.IsogenyQuotient.UniversalParameterKernels.representedKernels j arithmeticEmbedding hsplit M.space (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M)
      t.multiplierNat labels t.exponentNat Q repr).property v |>.1,
      (CMExtraction.IsogenyQuotient.UniversalParameterKernels.representedKernels j arithmeticEmbedding hsplit M.space (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M)
        t.multiplierNat labels t.exponentNat Q repr).property v |>.2.2⟩
  · intro T x H
    let H' : AbelianScheme.TateComparison.Subgroups.KernelChoices ((CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).pullback x.left)
        (fun v => j.localCharacter arithmeticEmbedding (labels v)) t.multiplierNat t.exponentNat :=
      ⟨H.val, fun v => by
        have hv := H.property v
        dsimp only at hv
        rw [hχ v] at hv
        exact hv⟩
    let e := CMExtraction.IsogenyQuotient.ParameterKernels.parameterFiberKernelEquiv j arithmeticEmbedding hsplit M.space (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M)
      t.multiplierNat labels t.exponentNat Q repr T x
    let c := e.symm H'
    have branch (b : AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.SourceFiber (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q) x) (v : Fin s) :
        CMExtraction.IsogenyQuotient.FineKernelData.chosenKernelAtLift M (parameterCorrespondence M Q dst hQf hQe) t χ f x b.val b.property v =
          (e b).val v := by
      unfold CMExtraction.IsogenyQuotient.FineKernelData.chosenKernelAtLift
      rw [hkernel]
      exact CMExtraction.IsogenyQuotient.UniversalParameterKernels.representedKernels_at_branch j arithmeticEmbedding hsplit M.space (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M)
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

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.FineClassification.CM
