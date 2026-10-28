import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cm
import OAI.NumberTheory.Approximation.Weak
import OAI.Geometry.ComplexBall.Fields
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.StandardLattice

/-! # Ball Datum -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallDatum.CM

noncomputable section

/-! Construct the actual Hermitian coefficient and full integral lattice
required by ThetaCycle. Weak approximation is supplied by the proved WeakApproximation theorem. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.StandardLattice.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

omit [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K] in
theorem standard_lattice_stable (a : NumberField.RingOfIntegers K)
    (x : HeckeCycles.GeometricSource.CM.Vec K) (hx : x ∈ HeckeCycles.StandardLattice.CM.standardLattice K) :
    (a : K) • x ∈ HeckeCycles.StandardLattice.CM.standardLattice K := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨a • y, ?_⟩
  ext1 i
  exact map_mul (algebraMap (NumberField.RingOfIntegers K) K) a (y i)

theorem exists_ball_datum
    (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) :
    Nonempty (HeckeCycles.GeometricSource.CM.BallDatum K) := by
  have hWeakApproximation : Geometry.ComplexBall.Fields.ArithmeticQuotient.WeakApproximationInput K := by
    intro ι hι v hn hd
    exact NumberTheory.Approximation.Weak.HodgeWeakApproximation.weak_approximation K v hn hd
  obtain ⟨b, hb, hb0, hnegative, hdefinite⟩ :=
    Geometry.ComplexBall.Fields.ArithmeticQuotient.exists_signature_coefficient hWeakApproximation K.val.toRingHom
  refine ⟨⟨b, hb, hnegative, ?_, hother, HeckeCycles.StandardLattice.CM.standardLattice K,
    HeckeCycles.StandardLattice.CM.standardLattice_fg K, HeckeCycles.StandardLattice.CM.standardLattice_full K, standard_lattice_stable K⟩⟩
  intro τ hτ hc
  apply hdefinite (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ).toRingHom
  · intro he
    apply hτ
    apply (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K).injective
    ext x
    exact congrArg (fun f : K →+* ℂ => f x) he
  · intro he
    apply hc
    apply (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K).injective
    ext x
    exact (congrArg (fun f : K →+* ℂ => f x) he).trans (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_coe K x).symm

/-- The same definite place proves anisotropy of the constructed ball data. -/
theorem ball_datum_anisotropic (B : HeckeCycles.GeometricSource.CM.BallDatum K) (x : HeckeCycles.GeometricSource.CM.Vec K)
    (hx : HeckeCycles.GeometricSource.CM.hermitian K B.b x x = 0) : x = 0 := by
  obtain ⟨τ, hτ, hc⟩ := B.other_place
  exact Geometry.ComplexBall.Fields.ArithmeticQuotient.anisotropic_of_definite_embedding B.b
    (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ).toRingHom (B.definite τ hτ hc) x hx

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallDatum.CM
