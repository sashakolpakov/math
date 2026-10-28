import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedTowerIso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso

/-! # Action Tower Iso -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionTowerIso

noncomputable section

/-! The scalar-tower comparison retains the original integral action.
Its polarized component is the comparison already used for full kernels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedTowerIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockGroupComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockSplitting

variable {E : Type} [Field E] {S T U : Scheme} {d N : ℕ} {δ : Fin d → ℕ}

def actionBaseCongrIso (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E d δ N S)
    (f g : T ⟶ S) (w : f = g) : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso (A.pullback f) (A.pullback g) := by
  cases w
  exact PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.refl _

theorem actionBaseCongrIso_polarized (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E d δ N S)
    (f g : T ⟶ S) (w : f = g) :
    (actionBaseCongrIso A f g w).polarized = PolarizedTowerIso.polarizedBaseCongrIso A.polarized f g w := by
  cases w
  rfl

def actionIteratedIso (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E d δ N S)
    (f : T ⟶ S) (h : U ⟶ T) (g : U ⟶ S) (w : h ≫ f = g) :
    PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso ((A.pullback f).pullback h) (A.pullback g) :=
  (PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackComp A f h).trans (actionBaseCongrIso A (h ≫ f) g w)

theorem actionIteratedIso_polarized (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E d δ N S)
    (f : T ⟶ S) (h : U ⟶ T) (g : U ⟶ S) (w : h ≫ f = g) :
    (actionIteratedIso A f h g w).polarized = PolarizedTowerIso.polarizedIteratedIso A.polarized f h g w := by
  change (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A.polarized f h).trans
    (actionBaseCongrIso A (h ≫ f) g w).polarized = _
  rw [actionBaseCongrIso_polarized]
  rfl

variable (R F L : Type) [CommRing R] [IsLocalRing R] [Field F] [Field L]
  [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E d δ N (Spec (.of R))) (v : EvaluationDVRLifts.EvaluationDVR R L)

def evaluatedIntegralActionIso :=
  (actionIteratedIso A
    (Spec.map (CommRingCat.ofHom (algebraMap R F)))
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (Spec.map (CommRingCat.ofHom (algebraMap R L))) (Evaluated.BlockSplitting.algebraTowerBaseComp R F L)).trans
  (actionIteratedIso A
    (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier)))
    (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))
    (Spec.map (CommRingCat.ofHom (algebraMap R L))) (Evaluated.BlockSplitting.algebraTowerBaseComp R v.carrier L)).symm

theorem evaluatedIntegralActionIso_polarized :
    (evaluatedIntegralActionIso R F L A v).polarized =
      PolarizedTowerIso.evaluatedIntegralPolarizedIso R F L A.polarized v := by
  change (actionIteratedIso A _ _ _ (Evaluated.BlockSplitting.algebraTowerBaseComp R F L)).polarized.trans
    (actionIteratedIso A _ _ _ (Evaluated.BlockSplitting.algebraTowerBaseComp R v.carrier L)).polarized.symm = _
  rw [actionIteratedIso_polarized, actionIteratedIso_polarized]
  rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionTowerIso
