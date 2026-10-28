import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionPairingSourceData
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.KernelIsoComparison

/-! # Action Kernel Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionKernelComparison.PairingSourceData

noncomputable section

/-! Transport a complete coefficient kernel at the coherent polarized
action-source index. Block squares and pairings are constructed fields;
the active-family equality is the only remaining comparison input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionBlockPairingIso.Polarized
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.KernelIsoComparison

local instance actionKernelPullbackMonoidal {X Y : Scheme} (h : X ⟶ Y) :
    (Over.pullback h).Monoidal := Over.instBraidedPullback.toMonoidal

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {S T Q : Scheme} [IsReduced S] [IsLocallyNoetherian S]
  [IsReduced T] [IsLocallyNoetherian T] [IsReduced Q] [IsLocallyNoetherian Q]
  {dim level : ℕ} {δ : Fin dim → ℕ}
  {A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E dim δ level S}
  {B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E dim δ level T} {f : Q ⟶ S} {g : Q ⟶ T}

def _root_.OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionPairingSourceData.ActionPairingSource.fullKernelComparison (C : ActionPairingSourceData.ActionPairingSource A B f g)
    (n : ℕ) (hn : 0 < n) {s : ℕ}
    (chosen opposite : Fin s → NumberField.RingOfIntegers E)
    (D : ∀ v, C.BlockIso n (chosen v)) (H : ∀ v, C.BlockIso n (opposite v))
    (active : Fin s) (c : Fin s → Bool)
    (F₀ : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.polarized.abelian.scheme (Over.mk f))
    (F₁ : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup B.polarized.abelian.scheme (Over.mk g)) :=
  PLift.up (Parameter.KernelIsoComparison.parameter_fullKernel_iso_comparison f g
    (Grp.mk A.polarized.abelian.scheme) (Grp.mk B.polarized.abelian.scheme) C.groupIso
    (fun v => Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (A.action.map (chosen v))))
    (fun v => Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (A.action.map (opposite v))))
    (fun v => Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (B.action.map (chosen v))))
    (fun v => Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (B.action.map (opposite v))))
    (fun v => (D v).iso) (fun v => (H v).iso)
    (fun v => Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (A.action.map (chosen v))))
    (fun v => Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (B.action.map (chosen v))))
    (fun v => Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (A.action.map (opposite v))))
    (fun v => Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (B.action.map (opposite v))))
    (fun v => ActionBlockPairingIso.Polarized.canonicalActionBlockPairing A.polarized A.action n hn (chosen v) (opposite v))
    (fun v => ActionBlockPairingIso.Polarized.canonicalActionBlockPairing B.polarized B.action n hn (chosen v) (opposite v))
    active c F₀ F₁ (fun v => (D v).inclusion) (fun v => (H v).inclusion)
    (fun v => (C.blockIsoPairing n hn (chosen v) (opposite v) (D v) (H v)).down))

def _root_.OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionPairingSourceData.ActionPairingSource.fullKernelComparisonFromComponents
    (C : ActionPairingSourceData.ActionPairingSource A B f g)
    (n : ℕ) (hn : 0 < n) {s : ℕ}
    (chosen opposite : Fin s → NumberField.RingOfIntegers E)
    (D : ∀ v, (Over.pullback f).mapGrp.obj
        (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (A.action.map (chosen v)))) ≅
      (Over.pullback g).mapGrp.obj
        (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (B.action.map (chosen v)))))
    (H : ∀ v, (Over.pullback f).mapGrp.obj
        (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (A.action.map (opposite v)))) ≅
      (Over.pullback g).mapGrp.obj
        (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (B.action.map (opposite v)))))
    (hD : ∀ v, (D v).hom.hom.hom ≫
        (Over.pullback g).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (B.action.map (chosen v))) =
      (Over.pullback f).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (A.action.map (chosen v))) ≫ C.map)
    (hH : ∀ v, (H v).hom.hom.hom ≫
        (Over.pullback g).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (B.action.map (opposite v))) =
      (Over.pullback f).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (A.action.map (opposite v))) ≫ C.map)
    (active : Fin s) (c : Fin s → Bool)
    (F₀ : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.polarized.abelian.scheme (Over.mk f))
    (F₁ : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup B.polarized.abelian.scheme (Over.mk g)) :=
  PLift.up (Parameter.KernelIsoComparison.parameter_fullKernel_iso_comparison f g
    (Grp.mk A.polarized.abelian.scheme) (Grp.mk B.polarized.abelian.scheme) C.groupIso
    (fun v => Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (A.action.map (chosen v))))
    (fun v => Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (A.action.map (opposite v))))
    (fun v => Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (B.action.map (chosen v))))
    (fun v => Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (B.action.map (opposite v))))
    D H
    (fun v => Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (A.action.map (chosen v))))
    (fun v => Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (B.action.map (chosen v))))
    (fun v => Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (A.action.map (opposite v))))
    (fun v => Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (B.action.map (opposite v))))
    (fun v => ActionBlockPairingIso.Polarized.canonicalActionBlockPairing A.polarized A.action n hn (chosen v) (opposite v))
    (fun v => ActionBlockPairingIso.Polarized.canonicalActionBlockPairing B.polarized B.action n hn (chosen v) (opposite v))
    active c F₀ F₁ hD hH
    (fun v => (C.blockPairingComparison n hn (chosen v) (opposite v)).down
      (D v).hom (H v).hom (hD v) (hH v)))

def _root_.OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionKernelComparison.fullKernelComparisonFromPolarizedActions
    (A₀ : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel dim δ level S)
    (B₀ : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel dim δ level T)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A₀.abelian)
    (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B₀.abelian)
    (f : Q ⟶ S) (g : Q ⟶ T)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A₀.pullback f) (B₀.pullback g))
    (groupIso : (Over.pullback f).mapGrp.obj (Grp.mk A₀.abelian.scheme) ≅
      (Over.pullback g).mapGrp.obj (Grp.mk B₀.abelian.scheme))
    (map_eq : e.abelian.hom = groupIso.hom.hom.hom)
    (n : ℕ) (hn : 0 < n) {s : ℕ}
    (chosen opposite : Fin s → NumberField.RingOfIntegers E)
    (D : ∀ v, (Over.pullback f).mapGrp.obj
        (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (ρ.map (chosen v)))) ≅
      (Over.pullback g).mapGrp.obj
        (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (σ.map (chosen v)))))
    (H : ∀ v, (Over.pullback f).mapGrp.obj
        (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (ρ.map (opposite v)))) ≅
      (Over.pullback g).mapGrp.obj
        (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (σ.map (opposite v)))))
    (hD : ∀ v, (D v).hom.hom.hom ≫
        (Over.pullback g).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (σ.map (chosen v))) =
      (Over.pullback f).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (ρ.map (chosen v))) ≫ groupIso.hom.hom.hom)
    (hH : ∀ v, (H v).hom.hom.hom ≫
        (Over.pullback g).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (σ.map (opposite v))) =
      (Over.pullback f).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (ρ.map (opposite v))) ≫ groupIso.hom.hom.hom)
    (active : Fin s) (c : Fin s → Bool)
    (F₀ : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A₀.abelian.scheme (Over.mk f))
    (F₁ : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup B₀.abelian.scheme (Over.mk g)) :=
  PLift.up (Parameter.KernelIsoComparison.parameter_fullKernel_iso_comparison f g
    (Grp.mk A₀.abelian.scheme) (Grp.mk B₀.abelian.scheme) groupIso
    (fun v => Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (ρ.map (chosen v))))
    (fun v => Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (ρ.map (opposite v))))
    (fun v => Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (σ.map (chosen v))))
    (fun v => Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (σ.map (opposite v))))
    D H
    (fun v => Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (ρ.map (chosen v))))
    (fun v => Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (σ.map (chosen v))))
    (fun v => Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (ρ.map (opposite v))))
    (fun v => Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (σ.map (opposite v))))
    (fun v => ActionBlockPairingIso.Polarized.canonicalActionBlockPairing A₀ ρ n hn (chosen v) (opposite v))
    (fun v => ActionBlockPairingIso.Polarized.canonicalActionBlockPairing B₀ σ n hn (chosen v) (opposite v))
    active c F₀ F₁ hD hH
    (fun v => ActionBlockPairingIso.Polarized.polarizedActionBlockPairing_iso
      A₀ B₀ ρ σ f g e groupIso.hom.hom.hom map_eq n hn (chosen v) (opposite v)
      (D v).hom (H v).hom (hD v) (hH v)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionKernelComparison.PairingSourceData
