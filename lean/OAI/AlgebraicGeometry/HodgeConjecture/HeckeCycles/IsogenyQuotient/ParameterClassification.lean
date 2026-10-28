import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.FineClassification
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.FineProjectors
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.KernelBlocks

/-! # Parameter Classification -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.ParameterClassification.CM

noncomputable section

/-! The exact full chosen/opposite kernel of a native IsogenyQuotient quotient
implies the original fine-model chosen-kernel classification. The raw
integral action is identified with the same universal action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.KernelBlocks

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] [Field L] [NumberField L] {κ : L →+* ℂ}
  {s N q : ℕ} [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (aE : E →+* L) (hsplit : j.HasSplitCoordinates aE)
  (t : AbelianScheme.TateComparison.Local.IntegralType s) (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).abelian)

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
local instance (v : Fin s) : Module (ZMod (q ^ t.multiplierNat))
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (t.exponentNat v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q t.multiplierNat (t.exponentNat v) (t.exponentNat_le v)

abbrev chosenProjectors := AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j aE hsplit (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).abelian σ t.multiplierNat s labels
abbrev oppositeProjectors := AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j aE hsplit (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).abelian σ t.multiplierNat s labels

abbrev subgroupFunctor : (Over M.space.left)ᵒᵖ ⥤ Type 1 :=
  AbelianScheme.IsogenyQuotient.Parameter.Products.Construction.blockTupleFunctor s (fun v => AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedSubgroupFunctor (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).abelian.scheme
    (q ^ t.multiplierNat) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (t.exponentNat v))
    (chosenProjectors M j aE hsplit t labels σ v))

variable (Q : Over M.space.left)
  (repr : (subgroupFunctor M j aE hsplit t labels σ).RepresentableBy Q)

abbrev choices := AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.universalBlockChoice (q ^ t.multiplierNat) s
  (fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (t.exponentNat v))
  (chosenProjectors M j aE hsplit t labels σ) repr

variable {W : Over M.space.left} [GrpObj W]
  (ep : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
    (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ t.multiplierNat) (chosenProjectors M j aE hsplit t labels σ v))
    (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ t.multiplierNat) (oppositeProjectors M j aE hsplit t labels σ v)) (W := W))

abbrev fullKernel := AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel (q ^ t.multiplierNat) s
  (fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (t.exponentNat v))
  (chosenProjectors M j aE hsplit t labels σ) (oppositeProjectors M j aE hsplit t labels σ) ep
  (choices M j aE hsplit t labels σ Q repr)

variable (model : (fullKernel M j aE hsplit t labels σ Q repr ep).Model)
  (dst : AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter M.space Q ⟶ M.space) (hQf : IsFinite Q.hom) (hQe : Etale Q.hom)
  (f : CMExtraction.IsogenyQuotient.FineKernelData.UniversalIsogeny (q := q) M
    (FineClassification.CM.parameterCorrespondence M Q dst hQf hQe) t)
  (hker : ∀ (T : Over Q.left) (z : T ⟶ ((CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).abelian.pullback Q.hom).scheme),
    z ≫ f.isogeny.hom =
      (1 : T ⟶ ((CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).abelian.pullback (T := Q.left) dst.left).scheme) ↔
      ∃! w : T ⟶ (AbelianScheme.IsogenyQuotient.Subgroup.Construction.subgroupGroupScheme (fullKernel M j aE hsplit t labels σ Q repr ep) model).X,
        w ≫ AbelianScheme.IsogenyQuotient.Intrinsic.Stability.Construction.nativeSubgroupInclusion (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).abelian Q
          (fullKernel M j aE hsplit t labels σ Q repr ep) model = z)

include hker in
theorem classifies (hσ : AbelianScheme.TateComparison.PELAdapters.actionFromEnd (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).action = σ)
    (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])
    (hχ : ∀ v, χ (v, false) = j.localCharacter aE (labels (.inl v))) :
    CMExtraction.IsogenyQuotient.FineKernelData.ClassifiesChosenKernels M (FineClassification.CM.parameterCorrespondence M Q dst hQf hQe)
      t χ f := by
  subst σ
  apply FineClassification.CM.represented_isogeny_classifies M j aE hsplit
    (fun v => labels (.inl v)) t Q repr dst hQf hQe f χ hχ
  intro v
  change (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel f.isogeny.hom).inf
    (AbelianScheme.TateComparison.Subgroups.splitBlock ((CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).pullback Q.hom) (χ (v, false)) t.multiplierNat) = _
  rw [hχ v]
  exact CMExtraction.IsogenyQuotient.KernelBlocks.fullKernel_chosen_block j aE hsplit (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M) M.space.hom Q t.multiplierNat labels
    t.exponentNat ep (choices M j aE hsplit t labels (AbelianScheme.TateComparison.PELAdapters.actionFromEnd (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).action) Q repr)
    model f.isogeny hker v

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.ParameterClassification.CM
