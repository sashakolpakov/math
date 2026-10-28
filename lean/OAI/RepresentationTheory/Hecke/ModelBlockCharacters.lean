import OAI.RepresentationTheory.Hecke.ModelLieRanks
import OAI.RepresentationTheory.Hecke.BlockCharacters

/-! # Model Block Characters -/

namespace OAI.RepresentationTheory.Hecke.ModelBlockCharacters.OrdinaryCharacterIntrinsic

noncomputable section

/-! The arithmetic residue square identifies the PEL Lie character
with the coefficient character used by the actual ordinary block.
The equality is proved before evaluating it at any moduli point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : AlgebraicGeometry.PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q)
  (j : AlgebraicGeometry.PELModuli.CMPoints.Arithmetic.QadicChoice K κ q)

/-- Compatibility of the two actual residue maps on the coefficient
ring. It contains no points, Lie ranks, operators or neighbor equations. -/
def CoefficientResidueSquare : Prop :=
  D.residue.comp (B.integralEmbedding iota) =
    (BlockCharacters.OrdinaryCharacterIntrinsic.blockResidueCast (k := ZMod q)).comp (j.residueCharacter iota 1 1)

omit [NumberField.IsCMField E] in
theorem residueCharacter_conjugate (τ : Gal(E/ℚ)) :
    (j.residueCharacter iota 1 1).comp (NumberField.RingOfIntegers.mapRingHom τ.toRingHom) =
      j.residueCharacter iota τ 1 := by
  ext a
  rfl

theorem modelLieCharacter_eq_block (hres : CoefficientResidueSquare D j) (τ : Gal(E/ℚ)) :
    ModelLieRanks.OrdinaryCharacterIntrinsic.modelLieCharacter D τ = BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter (k := AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) j iota τ := by
  have hc : (algebraMap (ZMod q) (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)).comp
      (BlockCharacters.OrdinaryCharacterIntrinsic.blockResidueCast (k := ZMod q) (q := q)) =
        BlockCharacters.OrdinaryCharacterIntrinsic.blockResidueCast (k := AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) (q := q) := Subsingleton.elim _ _
  ext a
  have hr := congrArg (algebraMap (ZMod q) (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))
    (RingHom.congr_fun hres (NumberField.RingOfIntegers.mapRingHom τ.toRingHom a))
  have ht := RingHom.congr_fun (residueCharacter_conjugate (iota := iota) j τ) a
  exact hr.trans
    ((congrArg (fun z => algebraMap (ZMod q) (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
      (BlockCharacters.OrdinaryCharacterIntrinsic.blockResidueCast (k := ZMod q) (q := q) z)) ht).trans
        (RingHom.congr_fun hc (j.residueCharacter iota τ 1 a)))

theorem modelPoint_blockLieRank (hres : CoefficientResidueSquare D j)
    (x : D.GeometricPoint) (τ : Gal(E/ℚ)) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (D.pointDatum x).data.polarized.abelian (D.pointDatum x).data.action
      (BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter (k := AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) j iota τ) (P.lieRank τ) :=
  (modelLieCharacter_eq_block D j hres τ) ▸ ModelLieRanks.OrdinaryCharacterIntrinsic.modelPoint_prescribedLieRank D x τ

end

end OAI.RepresentationTheory.Hecke.ModelBlockCharacters.OrdinaryCharacterIntrinsic
