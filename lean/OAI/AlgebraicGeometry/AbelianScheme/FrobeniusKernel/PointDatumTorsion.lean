import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport

/-! # Point Datum Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointDatumTorsion.Construction

noncomputable section

/-! The native moduli-point ordinary predicate counts precisely the
torsion of its full pulled-back PEL datum. The equivalence comes from
the actual universal family and retains the original point map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

private def torsionEquiv {S S' : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S')
    (T : Over S) (T' : Over S') (n : ℕ) :=
  A.torsionPoints n T ≃* B.torsionPoints n T'

private def torsionPullbackComposition {S S' S'' : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (h : S'' ⟶ S') (n : ℕ) :
    torsionEquiv (A.pullback (h ≫ f)) (A.pullback f)
      (Over.mk (𝟙 S'')) (Over.mk h) n := by
  let T : Over S'' := Over.mk (𝟙 _)
  let i : (Over.map h).obj T ≅ Over.mk h := Over.isoMk (Iso.refl _) (by rfl)
  let e := A.pullbackCompIso f h
  exact (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionPointsIso e n T).trans
    (((A.pullback f).torsionBaseChangeEquiv h T n).trans
      ((((A.pullback f).torsionFunctor n).mapIso i.symm.op).groupIsoToMulEquiv))

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

namespace SplitPELReduction

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)

def _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction.pointDatumTorsionEquiv (x : D.GeometricPoint) (n : ℕ) :
    torsionEquiv (g := 3 * s) (D.pointDatum x).data.polarized.abelian D.abelian
      (Over.mk (𝟙 (Spec (.of (ModuliPoint.Construction.residueClosure q))))) (Over.mk x.left) n :=
  torsionPullbackComposition D.integral.universal.data.polarized.abelian
    D.specialProjection x.left n

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction.isOrdinary_iff_pointDatum_count (x : D.GeometricPoint) :
    D.IsOrdinary x ↔
      Nat.card ((D.pointDatum x).data.polarized.abelian.torsionPoints q
        (Over.mk (𝟙 (Spec (.of (ModuliPoint.Construction.residueClosure q)))))) = q ^ (3 * s) := by
  change Nat.card (D.geometricTorsion x) = _ ↔ _
  rw [Nat.card_congr (D.pointDatumTorsionEquiv x q).toEquiv]

end SplitPELReduction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointDatumTorsion.Construction
