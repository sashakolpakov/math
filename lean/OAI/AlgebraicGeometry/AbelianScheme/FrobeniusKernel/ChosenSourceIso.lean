import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EquivariantBlockIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsChosenBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveSplittingSourceTransport

/-! # Chosen Source Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenSourceIso.Construction

noncomputable section

/-! Embedded active Frobenius pullback squares followed by a bundled
equivariant source isomorphism. The plane retains its original level-one
coordinates when included at level two. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {g : ℕ}
variable (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
variable (c : PolarizedComponents.Construction.EquivariantAbelianIso (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A) B
  (CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ) σ)

local notation "AF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A
local notation "ρF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ
local notation "sF" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime)
  (Spec (CommRingCat.of k)) (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))

def frobeniusSourceBlockIso (n : ℕ) (τ : Gal(E/ℚ)) :
    (Over.pullback sF).mapGrp.obj (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp ≅
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ n τ).toGrp :=
  IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A ρ sF n τ ≪≫
    EquivariantBlockIso.Construction.equivariantAbelianBlockIso j iota hsplit AF B ρF σ c n τ

variable (τ : Gal(E/ℚ))
variable (e : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp)
variable (e' : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ 1 τ).toGrp)

def frobeniusSourceActiveSplitting : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit
      (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A)
      (CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ) 1 τ).toGrp :=
  EquivariantBlockIso.Construction.equivariantAbelianBlockIso j iota hsplit AF B ρF σ c 1 τ ≪≫ e'

local notation "eF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenSourceIso.Construction.frobeniusSourceActiveSplitting j iota hsplit k A B ρ σ c τ e'

theorem frobeniusSourceLineBaseChangeIso_inclusion (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (PointsChosenBaseChange.Construction.l45FrobeniusLineBaseChangeIso j iota hsplit k A ρ τ e eF L).hom ≫
      (ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e' (CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit k A ρ τ e eF L)).hom.hom =
    (Over.pullback sF).map (ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e L).hom.hom ≫
      (frobeniusSourceBlockIso j iota hsplit k A B ρ σ c 1 τ).hom.hom.hom := by
  let b := EquivariantBlockIso.Construction.equivariantAbelianBlockIso j iota hsplit AF B ρF σ c 1 τ
  let L' := CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit k A ρ τ e eF L
  have ht := ActiveSplittingSourceTransport.Construction.chosenActiveEtaleLine_sourceTransport k q b e' L'
  have hs := congrArg (fun z : EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L' ⟶
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ 1 τ).toGrp => z.hom.hom) ht
  have hb := PointsChosenBaseChange.Construction.l45FrobeniusLineBaseChangeIso_inclusion j iota hsplit k A ρ τ e eF L
  change (ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q eF L').hom.hom ≫ b.hom.hom.hom = _ at hs
  rw [← hs, ← Category.assoc, hb]
  exact Category.assoc _ _ _

theorem frobeniusSourcePlaneBaseChangeIso_levelTwo :
    (PointsChosenBaseChange.Construction.l45FrobeniusPlaneBaseChangeIso j iota hsplit k A ρ τ e eF).hom ≫
      (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e' ≫
        CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit B σ τ (show 1 ≤ 2 by decide)).hom.hom =
    (Over.pullback sF).map (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e ≫
      CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit A ρ τ (show 1 ≤ 2 by decide)).hom.hom ≫
      (frobeniusSourceBlockIso j iota hsplit k A B ρ σ c 2 τ).hom.hom.hom := by
  let b₁ := EquivariantBlockIso.Construction.equivariantAbelianBlockIso j iota hsplit AF B ρF σ c 1 τ
  let b₂ := EquivariantBlockIso.Construction.equivariantAbelianBlockIso j iota hsplit AF B ρF σ c 2 τ
  let lF := CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit AF ρF τ (show 1 ≤ 2 by decide)
  let lT := CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit B σ τ (show 1 ≤ 2 by decide)
  have hl : lF ≫ b₂.hom = b₁.hom ≫ lT :=
    EquivariantBlockIso.Construction.equivariantAbelianBlockIso_level j iota hsplit AF B ρF σ c τ (show 1 ≤ 2 by decide)
  have hp := ActiveSplittingSourceTransport.Construction.chosenActiveEtalePlane_sourceTransport k q b₁ e'
  have ht : (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q eF ≫ lF) ≫ b₂.hom =
      ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e' ≫ lT := by
    rw [Category.assoc, hl, ← Category.assoc]
    exact congrArg (fun z => z ≫ lT) hp
  have hs := congrArg (fun z : EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q ⟶
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ 2 τ).toGrp => z.hom.hom) ht
  have hb := PointsChosenBaseChange.Construction.l45FrobeniusPlaneBaseChangeIso_levelTwo j iota hsplit k A ρ τ e eF
  change (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q eF ≫ lF).hom.hom ≫ b₂.hom.hom.hom = _ at hs
  rw [← hs, ← Category.assoc, hb]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenSourceIso.Construction
