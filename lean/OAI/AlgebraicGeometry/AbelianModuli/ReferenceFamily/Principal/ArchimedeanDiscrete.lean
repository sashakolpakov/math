import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.MatrixRealization
import OAI.RepresentationTheory.Theta.Geometric.StableCMArithmetic

/-! # Archimedean Discrete -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual principal lattice subgroup is discrete at the
distinguished complex place. Every omitted archimedean factor is compact,
as follows from the original embedding enumeration and signs. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

include hP in
theorem Datum.RankThreePELDatum.positive_other_embedding (ν : E →+* ℂ) (hν : ν ≠ P.μ) (hνc : ν ≠ (starRingEnd ℂ).comp P.μ) :
    0 < (ν P.b).re := by
  obtain ⟨⟨i, side⟩, hi⟩ := hP.1.2 ν.toRatAlgHom
  have hpos := hP.2.2.2.2.1
  cases side
  · have he : (P.embeddings i).toRingHom = ν := congrArg AlgHom.toRingHom hi
    have hne : i ≠ P.distinguished := by
      intro h
      subst i
      exact hν he.symm
    rw [← he]
    exact hpos i hne
  · have he : (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)).toRingHom = ν := congrArg AlgHom.toRingHom hi
    have hne : i ≠ P.distinguished := by
      intro h
      subst i
      exact hνc he.symm
    rw [← he]
    simpa [ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding] using hpos i hne

theorem Datum.RankThreePELDatum.principalArchimedean_le_stable (N : ℕ) :
    P.principalArchimedeanSubgroup N ≤
      (RepresentationTheory.Theta.Geometric.StableCMArithmetic.stableUnitarySubgroup P.lattice P.b).map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap P.b P.μ) := by
  rintro _ ⟨g, rfl⟩
  refine ⟨P.principalRationalMatrix N g, ?_, rfl⟩
  intro x
  rw [P.principalRationalMatrix_linear]
  exact (g.property.1.1 x).symm

include hP in
theorem Datum.RankThreePELDatum.principalArchimedean_discrete (N : ℕ) : DiscreteTopology (P.principalArchimedeanSubgroup N) := by
  let Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) := P.lattice
  have hL : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice P.lattice := hP.2.2.2.2.2.2.2.2.2.1
  have hL' : @NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice E _ DivisionRing.toRatAlgebra Λ :=
    (congrArg (fun A : Algebra ℚ E => @NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice E _ A Λ)
      (Subsingleton.elim (inferInstance : Algebra ℚ E) DivisionRing.toRatAlgebra)).mp hL
  have hb : NumberField.IsCMField.complexConj E P.b = P.b := hP.2.1
  have hb0 : P.b ≠ 0 := hP.2.2.1
  have hδ : NumberField.IsCMField.complexConj E P.imaginaryScalar = -P.imaginaryScalar := hP.2.2.2.2.2.2.2.1
  have hδ0 : P.imaginaryScalar ≠ 0 := hP.2.2.2.2.2.2.1
  let H := (RepresentationTheory.Theta.Geometric.StableCMArithmetic.stableUnitarySubgroup P.lattice P.b).map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap P.b P.μ)
  let : DiscreteTopology H := RepresentationTheory.Theta.Geometric.StableCMArithmetic.stableUnitary_archimedean_discrete P.lattice P.b hL' hb hb0
    P.imaginaryScalar hδ hδ0 P.μ (P.positive_other_embedding hP)
  let f : P.principalArchimedeanSubgroup N → H := fun g => ⟨g.val, P.principalArchimedean_le_stable N g.property⟩
  exact DiscreteTopology.of_continuous_injective (f := f) (continuous_subtype_val.subtype_mk _) (by
    intro g h he
    exact Subtype.ext (congrArg (fun t : H => t.val) he))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
