import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport

/-! # CM Points Lines -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsLines.Construction

noncomputable section

/-!
The Frobenius permutation of every active etale line is induced by the
actual native CMPoints block map and retains the original subgroup inclusion
into the source abelian scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {g : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

local notation "AF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A
local notation "ρF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ
local notation "F" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k A

variable (τ : Gal(E/ℚ))
variable (e : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp)
variable (targetSplitting : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit
    (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A)
    (CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ) 1 τ).toGrp)

def l45FrobeniusLineEquiv : EtaleSubgroups.Construction.ActiveEtaleLine q ≃ EtaleSubgroups.Construction.ActiveEtaleLine q :=
  EtaleLabelTransport.Construction.nativeActiveEtaleLineEquiv q k (CMPointsTransport.Construction.l45FrobeniusPlaneIso j iota hsplit k A ρ τ e targetSplitting)

def l45FrobeniusLineIso (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L ≅
      EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q (l45FrobeniusLineEquiv j iota hsplit k A ρ τ e targetSplitting L) :=
  EtaleLineTransport.Construction.activeEtaleLineSchemeIso q (Spec (.of k))
    (EtaleLabelTransport.Construction.activeEtaleLinearEquiv q k (CMPointsTransport.Construction.l45FrobeniusPlaneIso j iota hsplit k A ρ τ e targetSplitting)) L

theorem l45FrobeniusLineIso_inclusion (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (l45FrobeniusLineIso j iota hsplit k A ρ τ e targetSplitting L).hom ≫
      ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q targetSplitting (l45FrobeniusLineEquiv j iota hsplit k A ρ τ e targetSplitting L) =
    ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e L ≫ CMPointsTransport.Construction.l45FrobeniusBlockMap j iota hsplit k A ρ 1 τ := by
  have h := EtaleLineTransport.Construction.nativeActiveEtaleLineIso_embedding q k
    (CMPointsTransport.Construction.l45FrobeniusPlaneIso j iota hsplit k A ρ τ e targetSplitting) L
  have h' := congrArg (fun z => z ≫ ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q targetSplitting) h
  exact (Category.assoc (l45FrobeniusLineIso j iota hsplit k A ρ τ e targetSplitting L).hom
    (EtaleSubgroups.Construction.activeEtaleLineEmbedding _ q (l45FrobeniusLineEquiv j iota hsplit k A ρ τ e targetSplitting L))
    (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q targetSplitting)).symm.trans
      (h'.trans ((Category.assoc (EtaleSubgroups.Construction.activeEtaleLineEmbedding _ q L)
        (CMPointsTransport.Construction.l45FrobeniusPlaneIso j iota hsplit k A ρ τ e targetSplitting).hom
          (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q targetSplitting)).trans
            ((congrArg (fun z => EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L ≫ z)
              (CMPointsTransport.Construction.l45FrobeniusPlaneIso_inclusion j iota hsplit k A ρ τ e targetSplitting)).trans
                (Category.assoc _ _ _).symm)))

/-- The line transport square is an equality of actual native maps
into the abelian scheme and its Frobenius pullback. -/
theorem l45FrobeniusLineIso_abelian (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (l45FrobeniusLineIso j iota hsplit k A ρ τ e targetSplitting L).hom.hom.hom ≫
      ((ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q targetSplitting
        (l45FrobeniusLineEquiv j iota hsplit k A ρ τ e targetSplitting L)).hom.hom ≫
          CMPointsAt.Construction.l45BlockInclusion j iota hsplit AF ρF 1 τ) =
    ((ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e L).hom.hom ≫ CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ) ≫ (F).hom := by
  have h := congrArg
    (fun z : EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L ⟶
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit AF ρF 1 τ).toGrp => z.hom.hom)
    (l45FrobeniusLineIso_inclusion j iota hsplit k A ρ τ e targetSplitting L)
  change (l45FrobeniusLineIso j iota hsplit k A ρ τ e targetSplitting L).hom.hom.hom ≫
      (ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q targetSplitting
        (l45FrobeniusLineEquiv j iota hsplit k A ρ τ e targetSplitting L)).hom.hom =
    (ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e L).hom.hom ≫
      (CMPointsTransport.Construction.l45FrobeniusBlockMap j iota hsplit k A ρ 1 τ).hom.hom at h
  rw [← Category.assoc, h, Category.assoc, CMPointsTransport.Construction.l45FrobeniusBlockMap_inclusion, ← Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsLines.Construction
