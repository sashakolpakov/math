import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitBlockPullback
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Quotients

/-! # Residue Ordinary Splitting -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ResidueOrdinarySplitting.Ordinary

noncomputable section

/-! Express the original geometric ordinary splitting over the
actual residue field, with the constant etale plane required by the
integral component construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Quotients.Lifts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitBlockPullback

variable (q : ℕ) [Fact q.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)

def residueComparisonBase := Spec.map (CommRingCat.ofHom ρ.toRingHom)

theorem residueComparison_geometricBase :
    residueComparisonBase q R ρ ≫ Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ) = Lifts.closedBase R := by
  have h : CommRingCat.ofHom ρ.symm.toRingHom ≫ CommRingCat.ofHom ρ.toRingHom =
      𝟙 (CommRingCat.of (IsLocalRing.ResidueField R)) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext ρ.apply_symm_apply
  change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom ρ.symm.toRingHom) ≫ Lifts.closedBase R) = Lifts.closedBase R
  rw [← Category.assoc, ← Spec.map_comp, h, Spec.map_id, Category.id_comp]

def residueMultiplicativePart (d : ℕ) : Grp (Over (Spec (.of (IsLocalRing.ResidueField R)))) :=
  (Over.pullback (residueComparisonBase q R ρ)).mapGrp.obj (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q 1 d)

variable (A : Grp (Over (Spec (.of R)))) (d : ℕ)
  (e : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
    ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj A) q 1 d 2)

def residueOrdinaryGroupSplit :
    (Over.pullback (Lifts.closedBase R)).mapGrp.obj A ≅
      residueMultiplicativePart q R ρ d ⊗
        (Over.pullback (Lifts.closedBase R)).mapGrp.obj
          (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))) :=
  SplitBlockPullback.splitBlockPullbackIso A (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) (residueComparisonBase q R ρ)
    (Lifts.closedBase R) (residueComparison_geometricBase q R ρ)
    (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q 1 d) (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q 1 2) e ≪≫
      tensorIso (Iso.refl _) (EtaleBlockBaseChange.ordinaryEtalePrimeIso (IsLocalRing.ResidueField R) q 2 ≪≫
        (EtaleBlockBaseChange.etaleBlockBaseChangeIso (Lifts.closedBase R) (Multiplicative (Fin 2 → ZMod q))).symm)

def residueOrdinarySplit :
    (Over.pullback (Lifts.closedBase R)).obj A.X ≅
      (residueMultiplicativePart q R ρ d).X ⊗
        (Over.pullback (Lifts.closedBase R)).obj
          (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X :=
  (Grp.forget _).mapIso (residueOrdinaryGroupSplit q R ρ A d e)

instance residueOrdinarySplit_isMonHom : IsMonHom (residueOrdinarySplit q R ρ A d e).hom :=
  (residueOrdinaryGroupSplit q R ρ A d e).hom.hom.isMonHom_hom

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ResidueOrdinarySplitting.Ordinary
