import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointData

/-! # Model Lie Ranks -/

namespace OAI.RepresentationTheory.Hecke.ModelLieRanks.OrdinaryCharacterIntrinsic

noncomputable section

/-! The same prescribed PEL Lie ranks hold at every actual special
point. This extracts the integral universal family's full Lie condition
at the fixed geometric base map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : AlgebraicGeometry.PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q)

def modelGeometricScalar : B.R →+* AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q :=
  (algebraMap (ZMod q) (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)).comp D.residue

def modelLieCharacter (τ : Gal(E/ℚ)) : NumberField.RingOfIntegers E →+* AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q :=
  (modelGeometricScalar D).comp
    ((B.integralEmbedding iota).comp (NumberField.RingOfIntegers.mapRingHom τ.toRingHom))

theorem modelGeometricScalar_spec : Spec.map (CommRingCat.ofHom (modelGeometricScalar D)) =
    D.integralGeometricBase.hom :=
  Spec.map_comp (CommRingCat.ofHom D.residue)
    (CommRingCat.ofHom (algebraMap (ZMod q) (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)))

theorem modelPoint_prescribedLieRank (x : D.GeometricPoint) (τ : Gal(E/ℚ)) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (D.pointDatum x).data.polarized.abelian (D.pointDatum x).data.action
      (modelLieCharacter D τ) (P.lieRank τ) :=
  D.integral.universal.lieRanks (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) (modelGeometricScalar D)
    (D.geometricPointIntegralEquiv x).left
    ((D.geometricPointIntegralEquiv x).w.trans (modelGeometricScalar_spec D).symm) τ

end

end OAI.RepresentationTheory.Hecke.ModelLieRanks.OrdinaryCharacterIntrinsic
