import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.StandardResidueSplitting
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockRank
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces

/-! # Ordinary Splitting -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary

noncomputable section

/-! The active block of the original integral lift has the actual
ordinary special splitting, finite local freeness, and rank q^3. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.StandardResidueSplitting OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralIntrinsicBlock.Intrinsic OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockRank

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)

def liftedActiveBlock : Grp (Over (Spec (.of R))) :=
  GeometricBlockIso.nativeActionBlockGroup l.polarized.abelian l.action (q ^ 1) (j.projector iota hsplit 1 (labels (0, false)))

instance liftedActiveBlock_commutative : IsCommMonObj (liftedActiveBlock j hsplit labels l).X :=
  AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointScheme_commutative
    (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false)))))

def liftedActiveGeometricOrdinarySplit : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
    ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).mapGrp.obj
      (liftedActiveBlock j hsplit labels l)) q 1 1 2 :=
  GeometricBlockIso.liftedGeometricOrdinarySplitting j hsplit labels l O 1 0

def liftedActiveOrdinaryGroupSplit :=
  StandardResidueSplitting.standardResidueOrdinaryGroupSplit q R residueIso (liftedActiveBlock j hsplit labels l) 1
    (liftedActiveGeometricOrdinarySplit j hsplit labels O l)

def liftedActiveOrdinarySplit :=
  StandardResidueSplitting.standardResidueOrdinarySplit q R residueIso (liftedActiveBlock j hsplit labels l) 1
    (liftedActiveGeometricOrdinarySplit j hsplit labels O l)

instance liftedActiveOrdinarySplit_isMonHom : IsMonHom (liftedActiveOrdinarySplit j hsplit labels O l).hom :=
  (liftedActiveOrdinaryGroupSplit j hsplit labels O l).hom.hom.isMonHom_hom

theorem liftedActiveBlock_finiteLocallyFree :
    IsFinite (liftedActiveBlock j hsplit labels l).X.hom ∧
      Flat (liftedActiveBlock j hsplit labels l).X.hom ∧
      LocallyOfFinitePresentation (liftedActiveBlock j hsplit labels l).X.hom :=
  IntegralIntrinsicBlock.Intrinsic.integralNativeBlock_finiteLocallyFree j iota hsplit l.polarized l.action 1 (labels (0, false))

include O in
theorem liftedActiveBlock_rank (z : Spec (.of R)) :
    (liftedActiveBlock j hsplit labels l).X.hom.finrank z = q ^ 3 :=
  (BlockRank.integral_lift_nativeBlock_rank j hsplit labels O l 1 0 z).trans (by rw [pow_one])

theorem liftedActiveBlock_killed (T : Over (Spec (.of R)))
    (a : T ⟶ (liftedActiveBlock j hsplit labels l).X) : a ^ q = 1 := by
  have h : a ^ (q ^ 1) = 1 := congrArg Additive.toMul
    (Intrinsic.ActiveSubspaces.nativeBlockPoint_killed (q ^ 1)
      (l.action.map (j.projector iota hsplit 1 (labels (0, false)))) (Additive.ofMul a))
  exact (show a ^ q = a ^ (q ^ 1) by rw [pow_one]).trans h

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary
