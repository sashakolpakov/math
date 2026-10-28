import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UniqueKernels
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Models

/-! # Data -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.Data.CM

noncomputable section

/-! Assemble the complete TateComparison one-step realization on the actual IntegralModel
spread, from the original fine-model correspondences and their proved
kernel classification. Group-map uniqueness is derived by cancellation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s N q : ℕ} [Fact q.Prime]
  {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K} {κ : K →+* ℂ}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ}
  (V : PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N M.space M.universal B)
  [Smooth V.toOver.hom]

abbrev space := (Over.pullback B.generic).obj V.toOver

instance space_smooth : Smooth (CM.space M V).hom := by
  change Smooth (pullback.snd V.toOver.hom B.generic)
  infer_instance

instance space_noetherian : IsLocallyNoetherian (CM.space M V).left :=
  LocallyOfFiniteType.isLocallyNoetherian (CM.space M V).hom

instance space_reduced : IsReduced (CM.space M V).left :=
  Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced (CM.space M V).hom

abbrev family : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N (CM.space M V).left :=
  (PELFamily.CM.Family.ofActionData V.universal.data).pullback
    (pullback.fst V.toOver.hom B.generic)

def familyIso :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso (family M V)
      ((CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).pullback (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap B.fieldExtension M.space V.genericIso)) := by
  rw [CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap_eq]
  exact PELFamily.CM.Isomorphisms.toFamilyIso V.familyIso

variable {r : ℕ} (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData V.toOver r) (e : (∐ D.S) ≅ V.toOver)
  (C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space)
  (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])

def correspondences (t : AbelianScheme.TateComparison.Local.IntegralType s) : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence (CM.space M V) :=
  CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence B.fieldExtension M.space V.genericIso (C t)

def data : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E B.extension.carrier s q :=
  Models.CM.Hecke.data V D e (correspondences M V C) χ

def isogeny (t : AbelianScheme.TateComparison.Local.IntegralType s) (f : CMExtraction.IsogenyQuotient.FineKernelData.UniversalIsogeny (q := q) M (C t) t) :
    (CM.data M V D e C χ).UniversalIsogeny t :=
  BranchKernels.CM.isogeny B.fieldExtension M.space V.genericIso
    (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M) (family M V) (CM.familyIso M V) (C t) f

theorem kernel_geometry (t : AbelianScheme.TateComparison.Local.IntegralType s) (f : CMExtraction.IsogenyQuotient.FineKernelData.UniversalIsogeny (q := q) M (C t) t)
    (hf : CMExtraction.IsogenyQuotient.FineKernelData.ClassifiesChosenKernels M (C t) t χ f) (v : Fin s) :
    ((CM.data M V D e C χ).universalChosenKernel t (isogeny M V D e C χ t f) v).HasFiniteEtaleModel ∧
      ((CM.data M V D e C χ).universalChosenKernel t (isogeny M V D e C χ t f) v).HasGeometricType
        q (t.exponentNat v) :=
  BranchKernels.CM.geometry B.fieldExtension M.space V.genericIso
    (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M) (family M V) (CM.familyIso M V) (C t) f
    (χ (v, false)) t.multiplierNat (t.exponentNat v) (hf.1 v).1 (hf.1 v).2

theorem classifies (t : AbelianScheme.TateComparison.Local.IntegralType s) (f : CMExtraction.IsogenyQuotient.FineKernelData.UniversalIsogeny (q := q) M (C t) t)
    (hf : CMExtraction.IsogenyQuotient.FineKernelData.ClassifiesChosenKernels M (C t) t χ f)
    (T : Over (Spec (.of B.extension.carrier))) (x : T ⟶ (CM.data M V D e C χ).space)
    (H : (CM.data M V D e C χ).chosenKernels t x) :
    ∃! c : T ⟶ ((CM.data M V D e C χ).correspondence t).cover,
      ∃ w : c ≫ ((CM.data M V D e C χ).correspondence t).source = x,
        ∀ v, (CM.data M V D e C χ).chosenKernelAtLift t (isogeny M V D e C χ t f) x c w v = H.val v :=
  UniqueKernels.CM.at_test M B.fieldExtension V.genericIso
    (family M V) (CM.familyIso M V) (C t) t χ f hf T x H

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.Data.CM
