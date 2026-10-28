import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockSplitting

/-! # Evaluated Block Splitting -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.EvaluatedBlockSplitting

noncomputable section

/-! A splitting of the original generic native block gives a
splitting of its evaluated integral model through the constructed
block and scalar-tower comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockSplitting

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (R F L : Type) [CommRing R] [IsLocalRing R] [Field F] [Field L]
  [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of R)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (v : EvaluationDVRLifts.EvaluationDVR R L) (n : ℕ) (τ : Gal(E/ℚ))

def nativeEvaluatedBlockSplitting {I : Type}
    (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) ((ρ.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
          (j.projector iota hsplit n τ))))
    {H : Over (Spec (.of v.carrier))}
    (eH : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier)))).obj
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ))) ≅ H) :
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).obj H :=
  e ≪≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).mapIso
    (BlockBaseChange.nativeBlockBaseChangeIso j iota hsplit A ρ
      (Spec.map (CommRingCat.ofHom (algebraMap R F))) n τ).symm ≪≫
    Evaluated.BlockSplitting.evaluatedIntegralBlockIso R F L (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ))) v ≪≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).mapIso eH

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.EvaluatedBlockSplitting
