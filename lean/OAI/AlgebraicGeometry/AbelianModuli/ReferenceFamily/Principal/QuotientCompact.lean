import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.Anisotropy
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.RationalCongruence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.OrbitRealization
import OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicCompactness
import OAI.Geometry.ComplexBall.QuotientCompact

/-! # Quotient Compact -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Compactness of the literal principal orbit quotient at every
nonzero level, from the datum's given Hermitian anisotropy. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) (N : ℕ) (hN : N ≠ 0)

include hP hN in
theorem Datum.RankThreePELDatum.principalArchimedeanCosets_compact :
    CompactSpace (Geometry.ComplexBall.ArithmeticQuotientEquationsData.ArchimedeanSU P.b P.μ ⧸ P.principalArchimedeanSubgroup N) := by
  let Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) := P.lattice
  have hL : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice P.lattice := hP.2.2.2.2.2.2.2.2.2.1
  have hL' : @NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice E _ DivisionRing.toRatAlgebra Λ :=
    (congrArg (fun A : Algebra ℚ E => @NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice E _ A Λ)
      (Subsingleton.elim (inferInstance : Algebra ℚ E) DivisionRing.toRatAlgebra)).mp hL
  have hb : NumberField.IsCMField.complexConj E P.b = P.b := hP.2.1
  have hb0 : P.b ≠ 0 := hP.2.2.1
  have hδ : NumberField.IsCMField.complexConj E P.imaginaryScalar = -P.imaginaryScalar := hP.2.2.2.2.2.2.2.1
  have hδ0 : P.imaginaryScalar ≠ 0 := hP.2.2.2.2.2.2.1
  let G := Geometry.ComplexBall.Connected.ArithmeticQuotient.originalConnectedSemisimpleUnitaryGroup P.b hb hb0 P.imaginaryScalar hδ hδ0
  have hm := RepresentationTheory.Theta.Geometric.StableCMArithmetic.stableUnitary_arithmeticPresentation P.lattice P.b hL' hb hb0
    P.imaginaryScalar hδ hδ0 P.μ (P.positive_other_embedding hP)
  have hc := NumberTheory.ArithmeticGroups.Lattices.AnisotropicCompactness.Construction.arithmetic_compact_of_anisotropic G
    (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap P.b P.μ) (RepresentationTheory.Theta.Geometric.StableCMArithmetic.stableUnitarySubgroup P.lattice P.b)
    (P.principalRationalMatrixHom N).range hm (P.principalRational_commensurable N hP hN)
    (P.principalAlgebraicGroup_anisotropic hP)
  rw [MonoidHom.map_range] at hc
  exact hc

include hP hN in
theorem Datum.RankThreePELDatum.principalOrbitQuotient_compact : CompactSpace (Quotient (P.principalOrbitSetoid N)) := by
  let := P.principalArchimedeanCosets_compact hP N hN
  have him : (P.μ P.b).im = 0 := by
    have h := congrArg P.μ hP.2.1
    rw [NumberField.IsCMField.complexEmbedding_complexConj] at h
    exact Complex.conj_eq_iff_im.mp h
  let := Geometry.ComplexBall.QuotientCompact.Arithmetic.ballQuotient_compact (P.μ P.b) him hP.2.2.2.1 (P.principalArchimedeanSubgroup N)
  exact (P.principalOrbitHomeomorph N).symm.compactSpace

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
