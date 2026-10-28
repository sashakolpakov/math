import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActionBlockIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionKernelComparison

/-! # Kernel Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.KernelComparison

noncomputable section

/-! Compare the full kernels through the actual evaluated source and block isomorphisms. Only the active-family equality remains to be supplied by its original-parameter construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockPointComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericBlockInclusion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingSourceMaps.PolarizedIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActionBlockTorsionInclusion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedBlockPairingIso

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x) (v : EvaluationDVRLifts.EvaluationDVR R L)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActionBlockIso.GenericPairing OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PairingBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.KernelIsoComparison

def chosenBlockIso (n : ℕ) (labels : (Fin s ⊕ Fin s) ≃ Gal(E/ℚ)) (w : Fin s) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).mapGrp.obj
        (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock
          (q ^ n) ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
            (j.projector iota hsplit n (labels (.inl w)))))) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).mapGrp.obj
        (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock
          (q ^ n) ((l.overEvaluationDVR v).action.map
            (j.projector iota hsplit n (labels (.inl w)))))) := by
  simpa only [Lifted.GeometricBlockIso.nativeActionBlockGroup] using
    (PairingBlockIso.evaluatedLiftGenericPairingBlockIso
      (F := F) j hsplit l v n (labels (.inl w)))

def oppositeBlockIso (n : ℕ) (labels : (Fin s ⊕ Fin s) ≃ Gal(E/ℚ)) (w : Fin s) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).mapGrp.obj
        (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock
          (q ^ n) ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
            (j.projector iota hsplit n (labels (.inr w)))))) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).mapGrp.obj
        (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock
          (q ^ n) ((l.overEvaluationDVR v).action.map
            (j.projector iota hsplit n (labels (.inr w)))))) := by
  simpa only [Lifted.GeometricBlockIso.nativeActionBlockGroup] using
    (PairingBlockIso.evaluatedLiftGenericPairingBlockIso
      (F := F) j hsplit l v n (labels (.inr w)))

abbrev chosenBlockInclusionComparison (n : ℕ) (labels : (Fin s ⊕ Fin s) ≃ Gal(E/ℚ)) (w : Fin s) :=
  GenericBlockInclusion.evaluatedLiftGenericBlockGroupIso_inclusion
    (F := F) j hsplit l v n (labels (.inl w))

abbrev oppositeBlockInclusionComparison (n : ℕ) (labels : (Fin s ⊕ Fin s) ≃ Gal(E/ℚ)) (w : Fin s) :=
  GenericBlockInclusion.evaluatedLiftGenericBlockGroupIso_inclusion
    (F := F) j hsplit l v n (labels (.inr w))

/-! The full kernel comparison is applied in mathematical stages so each
coefficient-block family and each ambient inclusion square is checked
independently. -/

abbrev polarizedKernelSource (n : ℕ) (labels : (Fin s ⊕ Fin s) ≃ Gal(E/ℚ)) :=
  ActionKernelComparison.fullKernelComparisonFromPolarizedActions
    (E := E) (s := s)
    (l.polarized.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F))))
    (l.overEvaluationDVR v).polarized
    (l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F))))
    (l.overEvaluationDVR v).action
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))
    (PairingSourceMaps.evaluatedPairingSourceIso (F := F) l v)
    (SourceGroupIso.evaluatedLiftGenericSourceGroupIso (F := F) l v)
    (PairingSourceMaps.evaluatedPairingSourceMap_eq (F := F) l v)
    (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)
    (fun w => j.projector iota hsplit n (labels (.inl w)))
    (fun w => j.projector iota hsplit n (labels (.inr w)))

abbrev polarizedKernelChosenBlocks (n : ℕ) (labels : (Fin s ⊕ Fin s) ≃ Gal(E/ℚ)) :=
  polarizedKernelSource (F := F) j hsplit l v n labels
    (chosenBlockIso (F := F) j hsplit l v n labels)

abbrev polarizedKernelBlocks (n : ℕ) (labels : (Fin s ⊕ Fin s) ≃ Gal(E/ℚ)) :=
  polarizedKernelChosenBlocks (F := F) j hsplit l v n labels
    (oppositeBlockIso (F := F) j hsplit l v n labels)

abbrev polarizedKernelChosenSquare (n : ℕ) (labels : (Fin s ⊕ Fin s) ≃ Gal(E/ℚ)) :=
  polarizedKernelBlocks (F := F) j hsplit l v n labels
    (chosenBlockInclusionComparison (F := F) j hsplit l v n labels)

abbrev polarizedKernelBlockSquares (n : ℕ) (labels : (Fin s ⊕ Fin s) ≃ Gal(E/ℚ)) :=
  polarizedKernelChosenSquare (F := F) j hsplit l v n labels
    (oppositeBlockInclusionComparison (F := F) j hsplit l v n labels)

abbrev polarizedKernelParameters (n : ℕ) (labels : (Fin s ⊕ Fin s) ≃ Gal(E/ℚ))
    (active : Fin s) (c : Fin s → Bool)
    (F₀ : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup
      (l.polarized.abelian.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).scheme
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L)))))
    (F₁ : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup (l.overEvaluationDVR v).polarized.abelian.scheme
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))))) :=
  polarizedKernelBlockSquares (F := F) j hsplit l v n labels active c F₀ F₁

def evaluatedFullKernelComparisonFromActive (n : ℕ) (labels : (Fin s ⊕ Fin s) ≃ Gal(E/ℚ))
    (active : Fin s) (c : Fin s → Bool)
    (F₀ : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup
      (l.polarized.abelian.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).scheme
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L)))))
    (F₁ : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup (l.overEvaluationDVR v).polarized.abelian.scheme
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))))) :=
  polarizedKernelParameters (F := F) j hsplit l v n labels active c F₀ F₁

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.KernelComparison
