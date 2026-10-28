import OAI.RepresentationTheory.Hecke.OrdinaryCompactType
import OAI.RepresentationTheory.Hecke.ModelBlockCharacters
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification

/-! # Uniform Compact Type -/

namespace OAI.RepresentationTheory.Hecke.UniformCompactType.OrdinaryCharacterIntrinsic

noncomputable section

/-! The native ordinary splitting's compact type is independent of the
point. Its value is forced by the same integral PEL signature at every
point and the commuting coefficient residue square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : AlgebraicGeometry.PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q)
  (j : AlgebraicGeometry.PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)

def prescribedCompactType (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1))
    (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ)) (v : Fin s) : Bool :=
  decide (P.lieRank (labels (v.succ, false)) ≠ 0)

def prescribedMultiplicativeType (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1))
    (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ)) : Fin (s + 1) → Bool :=
  Fin.cases false (prescribedCompactType P labels)

theorem ordinary_compact_prescribed (hres : ModelBlockCharacters.OrdinaryCharacterIntrinsic.CoefficientResidueSquare D j)
    (x : D.OrdinaryPoint) (v : Fin s) :
    O.compact x v = prescribedCompactType P labels v :=
  OrdinaryCompactType.OrdinaryCharacterIntrinsic.ordinaryCompact_eq_prescribed j iota hsplit
    (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action
    (labels (v.succ, false)) (O.compact x v) (O.splitting x 1 v.succ)
    (ModelBlockCharacters.OrdinaryCharacterIntrinsic.modelPoint_blockLieRank D j hres x.val (labels (v.succ, false)))

theorem ordinary_multiplicative_prescribed (hres : ModelBlockCharacters.OrdinaryCharacterIntrinsic.CoefficientResidueSquare D j)
    (x : D.OrdinaryPoint) :
    Fin.cases false (O.compact x) = prescribedMultiplicativeType P labels := by
  funext v
  refine Fin.cases ?_ (fun u => ?_) v
  · rfl
  · exact ordinary_compact_prescribed D j hsplit labels O hres x u

theorem ordinary_compact_constant (hres : ModelBlockCharacters.OrdinaryCharacterIntrinsic.CoefficientResidueSquare D j)
    (x y : D.OrdinaryPoint) : O.compact x = O.compact y := by
  funext v
  exact (ordinary_compact_prescribed D j hsplit labels O hres x v).trans
    (ordinary_compact_prescribed D j hsplit labels O hres y v).symm

end

end OAI.RepresentationTheory.Hecke.UniformCompactType.OrdinaryCharacterIntrinsic
