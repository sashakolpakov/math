import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ResidueOrdinarySplitting
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MultiplicativeBlockBaseChange

/-! # Standard Residue Splitting -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.StandardResidueSplitting

noncomputable section

/-! The actual residue splitting has the literal multiplicative
ordinary factor and the integral constant etale plane. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ResidueOrdinarySplitting.Ordinary OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MultiplicativeBlockBaseChange

variable (q : ℕ) [Fact q.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)

def residueMultiplicativeIso (d : ℕ) :
    ResidueOrdinarySplitting.Ordinary.residueMultiplicativePart q R ρ d ≅ AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (IsLocalRing.ResidueField R) q 1 d :=
  MultiplicativeBlockBaseChange.multiplicativeBlockRingHomBaseChangeIso (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) (IsLocalRing.ResidueField R) ρ.toRingHom q 1 d

variable (A : Grp (Over (Spec (.of R)))) (d : ℕ)
  (e : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
    ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj A) q 1 d 2)

def standardResidueOrdinaryGroupSplit :
    (Over.pullback (Lifts.closedBase R)).mapGrp.obj A ≅
      AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (IsLocalRing.ResidueField R) q 1 d ⊗
        (Over.pullback (Lifts.closedBase R)).mapGrp.obj
          (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))) :=
  ResidueOrdinarySplitting.Ordinary.residueOrdinaryGroupSplit q R ρ A d e ≪≫ tensorIso (residueMultiplicativeIso q R ρ d) (Iso.refl _)

def standardResidueOrdinarySplit :
    (Over.pullback (Lifts.closedBase R)).obj A.X ≅
      (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (IsLocalRing.ResidueField R) q 1 d).X ⊗
        (Over.pullback (Lifts.closedBase R)).obj
          (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X :=
  (Grp.forget _).mapIso (standardResidueOrdinaryGroupSplit q R ρ A d e)

instance standardResidueOrdinarySplit_isMonHom :
    IsMonHom (standardResidueOrdinarySplit q R ρ A d e).hom :=
  (standardResidueOrdinaryGroupSplit q R ρ A d e).hom.hom.isMonHom_hom

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.StandardResidueSplitting
