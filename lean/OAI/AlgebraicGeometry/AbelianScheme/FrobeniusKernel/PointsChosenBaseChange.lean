import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsLines
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsBlockBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleBaseChange

/-! # Points Chosen Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsChosenBaseChange.Construction

noncomputable section

/-! The actual Frobenius line permutation and the literal q-plane in
q-squared torsion satisfy native chosen-subgroup pullback squares. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {g : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

local notation "hchar" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)
local notation "sF" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (CommRingCat.of k)) hchar
local notation "AF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A
local notation "ρF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ

variable (τ : Gal(E/ℚ))
variable (e : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp)
variable (eF : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit
    (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A)
    (CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ) 1 τ).toGrp)

local instance l45FrobeniusLine_etale (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    Etale (EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L).X.hom := EtaleSubgroups.Construction.etaleGroupScheme_etale _ _

local instance l45FrobeniusPlane_etale :
    Etale (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X.hom := EtaleSubgroups.Construction.etaleGroupScheme_etale _ _

def l45FrobeniusLineBaseChangeIso (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (Over.pullback sF).obj (EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L).X ≅
      (EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q (CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit k A ρ τ e eF L)).X :=
  EtaleBaseChange.Construction.etaleFrobeniusBaseChangeIso q (Fact.out : q.Prime) hchar _
    ((Grp.forget _).mapIso (CMPointsLines.Construction.l45FrobeniusLineIso j iota hsplit k A ρ τ e eF L))

theorem l45FrobeniusLineBaseChangeIso_inclusion (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (l45FrobeniusLineBaseChangeIso j iota hsplit k A ρ τ e eF L).hom ≫
      (ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q eF (CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit k A ρ τ e eF L)).hom.hom =
      (Over.pullback sF).map (ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e L).hom.hom ≫
        (IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A ρ sF 1 τ).hom.hom.hom := by
  have hl := congrArg (fun z : EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L ⟶
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit AF ρF 1 τ).toGrp => z.hom.hom)
    (CMPointsLines.Construction.l45FrobeniusLineIso_inclusion j iota hsplit k A ρ τ e eF L)
  have hf := PointsBlockBaseChange.Construction.l45FrobeniusBlockMap_eq_baseChange j iota hsplit k A ρ 1 τ
  exact EtaleBaseChange.Construction.etaleFrobeniusBaseChangeIso_inclusion q (Fact.out : q.Prime) hchar
    (EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L).X
    ((Grp.forget _).mapIso (CMPointsLines.Construction.l45FrobeniusLineIso j iota hsplit k A ρ τ e eF L))
    (ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e L).hom.hom
    (ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q eF (CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit k A ρ τ e eF L)).hom.hom
    (IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A ρ sF 1 τ).hom.hom.hom
    (hl.trans (congrArg (fun z => (ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e L).hom.hom ≫ z) hf))

def l45FrobeniusPlaneBaseChangeIso :
    (Over.pullback sF).obj (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X ≅
      (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X :=
  EtaleBaseChange.Construction.etaleFrobeniusBaseChangeIso q (Fact.out : q.Prime) hchar _
    ((Grp.forget _).mapIso (CMPointsTransport.Construction.l45FrobeniusPlaneIso j iota hsplit k A ρ τ e eF))

theorem l45FrobeniusPlaneBaseChangeIso_levelTwo :
    (l45FrobeniusPlaneBaseChangeIso j iota hsplit k A ρ τ e eF).hom ≫
      (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q eF ≫
        CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit AF ρF τ (show 1 ≤ 2 by decide)).hom.hom =
      (Over.pullback sF).map (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e ≫
        CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit A ρ τ (show 1 ≤ 2 by decide)).hom.hom ≫
          (IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A ρ sF 2 τ).hom.hom.hom := by
  have hl := congrArg (fun z : EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q ⟶
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit AF ρF 2 τ).toGrp => z.hom.hom)
    (CMPointsTransport.Construction.l45FrobeniusPlaneIso_levelTwo j iota hsplit k A ρ τ e eF)
  have hf := PointsBlockBaseChange.Construction.l45FrobeniusBlockMap_eq_baseChange j iota hsplit k A ρ 2 τ
  exact EtaleBaseChange.Construction.etaleFrobeniusBaseChangeIso_inclusion q (Fact.out : q.Prime) hchar
    (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X
    ((Grp.forget _).mapIso (CMPointsTransport.Construction.l45FrobeniusPlaneIso j iota hsplit k A ρ τ e eF))
    (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e ≫
      CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit A ρ τ (show 1 ≤ 2 by decide)).hom.hom
    (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q eF ≫
      CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit AF ρF τ (show 1 ≤ 2 by decide)).hom.hom
    (IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A ρ sF 2 τ).hom.hom.hom
    (hl.trans (congrArg (fun z => (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e ≫
      CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit A ρ τ (show 1 ≤ 2 by decide)).hom.hom ≫ z) hf))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsChosenBaseChange.Construction
