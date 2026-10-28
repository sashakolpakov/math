import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedEtaleTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsLines

/-! # Points Frobenius Mixed Line -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointsFrobeniusMixedLine.CM

noncomputable section

/-! Compute the mixed q-block using the original abelian Frobenius,
the native CMPoints block inclusion and its constructed permutation of
etale lines. The one-step etale restriction is the quotient input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsLines.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedEtaleTransport

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {d : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) (τ : Gal(E/ℚ))

local notation "AF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A
local notation "ρF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ
local notation "F" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k A

variable (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp)
variable (eF : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit
  (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A) (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ) 1 τ).toGrp)

abbrev activeChart := e.inv.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ

abbrev targetPlane := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q eF).hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit
  (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A) (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ) 1 τ

omit [IsAlgClosed k] in
theorem native_frobenius_kills_multiplicative :
    MixedKernels.multiplicativeInclusion ≫ activeChart j iota hsplit k A ρ τ e ≫ (F).hom = 1 := by
  have hk : ((AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e).hom.hom ≫
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ) ≫ (F).hom = 1 := by
    apply (Picard.Homomorphisms.Kernel.Construction.kernelScheme_universal _ _ _).mpr
    exact Picard.Homomorphisms.Diagonalizable.Construction.factors_kernel_of_trivial_relativeFrobenius q (Fact.out : q.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))
      (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X A.scheme
      (AbelianScheme.FrobeniusKernel.Multiplicative.Construction.ordinaryMultiplicative_relativeFrobenius q k 1)
      ((AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e).hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ)
  change ((MixedKernels.multiplicativeInclusion ≫ e.inv.hom.hom) ≫
    AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ) ≫ (F).hom = 1 at hk
  simpa only [activeChart, Category.assoc] using hk

theorem native_frobenius_plane_square :
    MixedKernels.etaleImage (activeChart j iota hsplit k A ρ τ e) (F).hom =
      (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusPlaneIso j iota hsplit k A ρ τ e eF).hom.hom.hom ≫
        targetPlane j iota hsplit k A ρ τ eF := by
  have hp := congrArg (fun z => z.hom.hom)
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusPlaneIso_inclusion j iota hsplit k A ρ τ e eF)
  change (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusPlaneIso j iota hsplit k A ρ τ e eF).hom.hom.hom ≫
    (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q eF).hom.hom =
      (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom ≫ (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusBlockMap j iota hsplit k A ρ 1 τ).hom.hom at hp
  have ha := congrArg (fun z => z ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit AF ρF 1 τ) hp
  have hs : (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom = MixedKernels.etaleInclusion ≫ e.inv.hom.hom := rfl
  rw [hs] at ha
  simpa only [MixedKernels.etaleImage, activeChart, targetPlane, Category.assoc,
    AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusBlockMap_inclusion] using ha.symm

theorem native_frobenius_mixed_line {C : Over (Spec (.of k))} [GrpObj C]
    (g : (AF).scheme ⟶ C) (L : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (hsecond : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (targetPlane j iota hsplit k A ρ τ eF ≫ g)
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q
        (AbelianScheme.FrobeniusKernel.CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit k A ρ τ e eF L)).hom.hom) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (activeChart j iota hsplit k A ρ τ e ≫ (F).hom ≫ g)
      (𝟙 (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X ⊗ₘ
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L).hom.hom) := by
  have : IsClosedImmersion (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L).hom.hom.left :=
    AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding_closed (Spec (.of k)) q L
  have : Mono (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L).hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q
      (AbelianScheme.FrobeniusKernel.CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit k A ρ τ e eF L)).hom.hom.left :=
    AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding_closed (Spec (.of k)) q _
  have : Mono (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q
      (AbelianScheme.FrobeniusKernel.CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit k A ρ τ e eF L)).hom.hom := Over.mono_of_mono_left _
  have hline := congrArg (fun z => z.hom.hom)
    (AbelianScheme.FrobeniusKernel.EtaleLineTransport.Construction.nativeActiveEtaleLineIso_embedding q k (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusPlaneIso j iota hsplit k A ρ τ e eF) L)
  exact MixedEtaleTransport.mixed_kernel_from_target_etale
    (M := (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X)
    (E := (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X)
    (E' := (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X)
    (H := (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L).X)
    (H' := (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q
      (AbelianScheme.FrobeniusKernel.CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit k A ρ τ e eF L)).X)
    (activeChart j iota hsplit k A ρ τ e) (F).hom g
    (native_frobenius_kills_multiplicative j iota hsplit k A ρ τ e)
    (targetPlane j iota hsplit k A ρ τ eF)
    ((Grp.forget _).mapIso (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusPlaneIso j iota hsplit k A ρ τ e eF))
    ((Grp.forget _).mapIso (AbelianScheme.FrobeniusKernel.CMPointsLines.Construction.l45FrobeniusLineIso j iota hsplit k A ρ τ e eF L))
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L).hom.hom
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q
      (AbelianScheme.FrobeniusKernel.CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit k A ρ τ e eF L)).hom.hom
    (native_frobenius_plane_square j iota hsplit k A ρ τ e eF) hline.symm hsecond

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointsFrobeniusMixedLine.CM
