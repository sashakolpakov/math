import OAI.NumberTheory.ArithmeticGroups.Data

/-! # Datum -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum

noncomputable section

/-! The reference datum is an actual Hermitian lattice with an integral
polarization and the period family of CongruenceLevel. It contains no moduli scheme,
quotient identification, or arithmetic compactness/comparison assertion. -/

open scoped Classical

open OAI.NumberTheory.ArithmeticGroups.Data.CongruenceLevel

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

/-- Chosen marked-lattice input for the rank-three PEL problem.
The elementary-divisor type is related to the integral form by
`IsAdmissible`, rather than being an unconstrained moduli label. -/
structure RankThreePELDatum (s : ℕ) where
  embeddings : Fin s → E →ₐ[ℚ] ℂ
  distinguished : Fin s
  compactSigns : Fin s → Bool
  b : E
  imaginaryScalar : E
  denominator : ℕ
  lattice : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
  integralForm : lattice →ₗ[ℤ] lattice →ₗ[ℤ] ℤ
  polarizationType : Fin (3 * s) → ℕ
  periodFamily : Geometry.ComplexBall.PrescribedSignsB.BallChart → Submodule ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s))

namespace RankThreePELDatum

variable {E} {s : ℕ} (P : RankThreePELDatum E s)

def μ : E →+* ℂ := (P.embeddings P.distinguished).toRingHom

def traceForm (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : ℚ :=
  (P.denominator : ℚ) * Algebra.trace ℚ E
    (P.imaginaryScalar * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b x y)

def domain : Set Geometry.ComplexBall.PrescribedSignsB.BallChart :=
  {z | (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b])
    P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector z))).re < 0}

def firstLieRank (i : Fin s) : ℕ :=
  if i = P.distinguished then 2 else if P.compactSigns i then 3 else 0

/-- Lie ranks indexed by the manuscript's Galois automorphisms; the fixed
complex embedding identifies each automorphism with an embedding line. -/
def lieRank (τ : E ≃ₐ[ℚ] E) : ℕ :=
  ∑ i : Fin s,
    if P.μ.comp τ.toRingHom = (P.embeddings i).toRingHom then P.firstLieRank i
    else if P.μ.comp τ.toRingHom = (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)).toRingHom
      then 3 - P.firstLieRank i else 0

/-- The finite cokernel of the lattice polarization has the specified
elementary divisors, in the same doubled convention as HilbertConstruction. -/
def HasPolarizationType : Prop :=
  Nonempty (((P.lattice →ₗ[ℤ] ℤ) ⧸ P.integralForm.range) ≃+
    ((∀ i : Fin (3 * s), ZMod (P.polarizationType i)) ×
      (∀ i : Fin (3 * s), ZMod (P.polarizationType i))))

/-- Natural reference-data hypotheses. The period clause is exactly the
CongruenceLevel analytic fiber model; it asserts no family-to-scheme comparison. -/
def IsAdmissible : Prop :=
  Function.Bijective
    (fun p : Fin s × Bool => if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings p.1)
      else P.embeddings p.1) ∧
  NumberField.IsCMField.complexConj E P.b = P.b ∧
  P.b ≠ 0 ∧
  (P.μ P.b).re < 0 ∧
  (∀ i, i ≠ P.distinguished → 0 < (P.embeddings i P.b).re) ∧
  (∀ x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b x x = 0 → x = 0) ∧
  P.imaginaryScalar ≠ 0 ∧
  NumberField.IsCMField.complexConj E P.imaginaryScalar = -P.imaginaryScalar ∧
  0 < P.denominator ∧
  NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice P.lattice ∧
  (∀ x y : P.lattice, (P.integralForm x y : ℚ) = P.traceForm x y) ∧
  (∀ x : P.lattice, P.integralForm x x = 0) ∧
  (∀ x : P.lattice, (∀ y, P.integralForm x y = 0) → x = 0) ∧
  (∀ i, 0 < P.polarizationType i) ∧
  (∀ i j, i ≤ j → P.polarizationType i ∣ P.polarizationType j) ∧
  P.HasPolarizationType ∧
  Geometry.ComplexBall.PrescribedSignsB.HolomorphicFamily P.domain (3 * s) P.periodFamily ∧
  (∀ z ∈ P.domain,
    (∀ u, u ∈ P.periodFamily z ↔
      Geometry.ComplexBall.PrescribedSignsB.Prescribed (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b]))
        P.distinguished P.compactSigns z u) ∧
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.AnalyticPolarizedFiber P.embeddings P.lattice P.traceForm (P.periodFamily z))

end RankThreePELDatum

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum
