import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedPlace
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusKernelLifts

/-! # Restricted Place -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RestrictedPlace.CM

noncomputable section

/-! Apply the full NeighborCounting input over the original coefficient field using
the restricted actual arithmetic place. All split residue coefficients
of the source reduction are retained. -/

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K) {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)

abbrev choice : PELModuli.CMPoints.Arithmetic.QadicChoice K M.complexEmbedding q :=
  HeckeCycles.RestrictedPlace.CM.choice (algebraMap K M.arithmetic.extension.carrier)
    M.arithmetic.embedding_extends j

theorem localCharacter_eq (τ : Gal(E/ℚ)) :
    (choice M j).localCharacter M.iota τ = j.localCharacter M.extendedEmbedding τ :=
  HeckeCycles.RestrictedPlace.CM.localCharacter_eq (algebraMap K M.arithmetic.extension.carrier)
    M.arithmetic.embedding_extends j M.iota τ

theorem residueCharacter_eq (τ : Gal(E/ℚ)) (n : ℕ) :
    (choice M j).residueCharacter M.iota τ n = j.residueCharacter M.extendedEmbedding τ n :=
  HeckeCycles.RestrictedPlace.CM.residueCharacter_eq (algebraMap K M.arithmetic.extension.carrier)
    M.arithmetic.embedding_extends j M.iota τ n

theorem splitCoordinates (hsplit : j.HasSplitCoordinates M.extendedEmbedding) :
    (choice M j).HasSplitCoordinates M.iota :=
  HeckeCycles.RestrictedPlace.CM.splitCoordinates (algebraMap K M.arithmetic.extension.carrier)
    M.arithmetic.embedding_extends j M.iota hsplit

variable (hM : M.HasPrescribedBallPeriods)
  (hsplit : j.HasSplitCoordinates M.extendedEmbedding) (R : M.GoodIntegralReduction q j)
  (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ))
  (hlabels : ∀ (v : Fin M.s) (b : Bool),
    labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b))
  (a : M.Family)

theorem reduction_coefficients (n : ℕ) (r : NumberField.RingOfIntegers E) (v : Fin M.s × Bool) :
    (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).splitCoefficients n
      (Ideal.Quotient.mk _ r) v = (choice M j).residueCharacter M.iota (labels v) n r :=
  (AbelianScheme.FrobeniusKernel.CMPointsReductionAdapter.Construction.l45SplitPELReduction_coefficients M hM j hsplit R labels hlabels a n r v).trans
    (RingHom.congr_fun (residueCharacter_eq M j (labels v) n) r).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RestrictedPlace.CM
