import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsCoefficientSplitting

/-! # CM Points Reduction Adapter -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsReductionAdapter.Construction

noncomputable section

/-!
Each actual integral universal family in CMPoints supplies the native FrobeniusKernel
reduction. The arithmetic coefficient isomorphisms and their
compatibilities are constructed; the original PEL family is retained.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [NumberField.IsCMField E] [Field K] [NumberField K]
variable (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
variable {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
variable (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
variable (R : M.GoodIntegralReduction q j)
variable (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ))
variable (hlabels : ∀ (v : Fin M.s) (b : Bool),
  labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b))

def l45SplitPELReduction (a : M.Family) :
    Integral.Construction.SplitPELReduction (M.datum a) M.iota M.complexEmbedding (M.moduli a).space
      (M.moduli a).universal M.arithmetic q := {
    integral := M.integral a
    residue := R.residue
    smooth := by
      obtain ⟨_, _, _, _, _, _, hsmooth, _, _, _⟩ := hM.2.2 a
      exact hsmooth
    proper := by
      obtain ⟨_, _, _, _, _, _, _, hproper, _, _⟩ := hM.2.2 a
      exact hproper
    levelPrimeToQ := R.levelPrimeToQ a
    polarizationPrimeToQ := R.polarizationPrimeToQ a
    active := (labels.symm (PELModuli.CMPoints.Arithmetic.rationalConjugation E)).1
    splitCoefficients := CMPointsCoefficientSplitting.Construction.l45CoefficientSplitting j M.extendedEmbedding hsplit M.s labels
    compatible := CMPointsCoefficientSplitting.Construction.l45CoefficientSplitting_compatible j M.extendedEmbedding hsplit M.s labels
    conjugation := CMPointsCoefficientSplitting.Construction.l45CoefficientSplitting_conjugation j M.extendedEmbedding hsplit M.s labels hlabels }

theorem l45SplitPELReduction_integral (a : M.Family) :
    (l45SplitPELReduction M hM j hsplit R labels hlabels a).integral = M.integral a := rfl

theorem l45SplitPELReduction_specialBase (a : M.Family) :
    (l45SplitPELReduction M hM j hsplit R labels hlabels a).specialBase = R.specialBase := rfl

theorem l45SplitPELReduction_specialFiber (a : M.Family) :
    (l45SplitPELReduction M hM j hsplit R labels hlabels a).specialFiber = R.specialFiber a := rfl

theorem l45SplitPELReduction_coefficients (a : M.Family) (n : ℕ)
    (r : NumberField.RingOfIntegers E) (v : Fin M.s × Bool) :
    (l45SplitPELReduction M hM j hsplit R labels hlabels a).splitCoefficients n (Ideal.Quotient.mk _ r) v =
      j.residueCharacter M.extendedEmbedding (labels v) n r :=
  CMPointsCoefficientSplitting.Construction.l45CoefficientSplitting_apply j M.extendedEmbedding hsplit M.s labels n r v

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsReductionAdapter.Construction
