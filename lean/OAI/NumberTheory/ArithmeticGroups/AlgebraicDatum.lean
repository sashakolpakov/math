import OAI.NumberTheory.ArithmeticGroups.Data

/-! # Algebraic Datum -/

namespace OAI.NumberTheory.ArithmeticGroups.AlgebraicDatum.CongruenceLevel.Algebraic

noncomputable section

/-! The reference datum is an actual Hermitian lattice with an integral
polarization and the period family of CongruenceLevel. It contains no moduli scheme,
quotient identification, or arithmetic compactness/comparison assertion. -/

open scoped Classical

open OAI.NumberTheory.ArithmeticGroups.Data.CongruenceLevel

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

/-- The original analytic lattice and integral form, before algebraization. -/
structure ReferenceInput (Place : Type*) [Fintype Place] where
  embeddings : Place → E →ₐ[ℚ] ℂ
  distinguished : Place
  compactSigns : Place → Bool
  b : E
  imaginaryScalar : E
  denominator : ℕ
  lattice : Submodule ℤ (Data.CongruenceLevel.VE E)
  integralForm : lattice →ₗ[ℤ] lattice →ₗ[ℤ] ℤ
  periodFamily : Geometry.ComplexBall.PrescribedSignsB.BallChart → Submodule ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient (Place))

namespace ReferenceInput

variable {E} {Place : Type*} [Fintype Place] (P : ReferenceInput E Place)

def μ : E →+* ℂ := (P.embeddings P.distinguished).toRingHom

def traceForm (x y : Data.CongruenceLevel.VE E) : ℚ :=
  (P.denominator : ℚ) * Algebra.trace ℚ E
    (P.imaginaryScalar * Data.CongruenceLevel.hermitian P.b x y)

def domain : Set Geometry.ComplexBall.PrescribedSignsB.BallChart :=
  {z | (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b])
    P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector z))).re < 0}

def firstLieRank (i : Place) : ℕ :=
  if i = P.distinguished then 2 else if P.compactSigns i then 3 else 0

/-- Lie ranks indexed by the manuscript's Galois automorphisms; the fixed
complex embedding identifies each automorphism with an embedding line. -/
def lieRank (τ : E ≃ₐ[ℚ] E) : ℕ :=
  ∑ i : Place,
    if P.μ.comp τ.toRingHom = (P.embeddings i).toRingHom then P.firstLieRank i
    else if P.μ.comp τ.toRingHom = (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)).toRingHom
      then 3 - P.firstLieRank i else 0

/-- Natural reference-data hypotheses. The period clause is exactly the
CongruenceLevel analytic fiber model; it asserts no family-to-scheme comparison. -/
def IsAdmissible : Prop :=
  Function.Bijective
    (fun p : Place × Bool => if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings p.1)
      else P.embeddings p.1) ∧
  NumberField.IsCMField.complexConj E P.b = P.b ∧
  P.b ≠ 0 ∧
  (P.μ P.b).re < 0 ∧
  (∀ i, i ≠ P.distinguished → 0 < (P.embeddings i P.b).re) ∧
  P.imaginaryScalar ≠ 0 ∧
  NumberField.IsCMField.complexConj E P.imaginaryScalar = -P.imaginaryScalar ∧
  0 < P.denominator ∧
  Data.CongruenceLevel.FullStableLattice P.lattice ∧
  (∀ x y : P.lattice, (P.integralForm x y : ℚ) = P.traceForm x y) ∧
  (∀ x : P.lattice, P.integralForm x x = 0) ∧
  (∀ x : P.lattice, (∀ y, P.integralForm x y = 0) → x = 0) ∧
  Geometry.ComplexBall.PrescribedSignsB.HolomorphicFamily P.domain (3 * Fintype.card Place) P.periodFamily ∧
  (∀ z ∈ P.domain,
    (∀ u, u ∈ P.periodFamily z ↔
      Geometry.ComplexBall.PrescribedSignsB.Prescribed (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b]))
        P.distinguished P.compactSigns z u) ∧
    Data.CongruenceLevel.AnalyticPolarizedFiber P.embeddings P.lattice P.traceForm (P.periodFamily z))

end ReferenceInput

end

end OAI.NumberTheory.ArithmeticGroups.AlgebraicDatum.CongruenceLevel.Algebraic
