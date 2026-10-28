import OAI.RepresentationTheory.Hecke.ModelBlockCharacters

/-! # Coefficient Residue Square -/

namespace OAI.RepresentationTheory.Hecke.CoefficientResidueSquare.OrdinaryCharacterIntrinsic

noncomputable section

/-! The coefficient residue square follows from the actual integral
completion map and its residue. Equality of residue maps is proved using
the q-adic residue representatives. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {q : ℕ} [Fact q.Prime]

theorem padic_residue_hom_unique {T : Type} [CommRing T] [CharP T q]
    (f g : ℤ_[q] →+* T) : f = g := by
  ext z
  have hz : z - (z.zmodRepr : ℤ_[q]) ∈ Ideal.span ({(q : ℤ_[q])} : Set ℤ_[q]) := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    exact PadicInt.sub_zmodRepr_mem z
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hz
  have he (h : ℤ_[q] →+* T) : h z = (z.zmodRepr : T) := by
    have hh := congrArg h hc
    simp only [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, map_sub] at hh
    exact sub_eq_zero.mp hh
  exact (he f).trans (he g).symm

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : AlgebraicGeometry.PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ}
  (D : AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q) (j : AlgebraicGeometry.PELModuli.CMPoints.Arithmetic.QadicChoice K κ q)

omit [NumberField.IsCMField E] in
theorem completion_map_on_coefficients (b : B.R →+* ℤ_[q])
    (η : B.extension.carrier →+* ℚ_[q])
    (hgeneric : PadicInt.Coe.ringHom.comp b = η.comp B.toField)
    (hfield : η.comp (algebraMap K B.extension.carrier) =
      j.completion.toRingHom.comp (NumberField.FinitePlace.embedding j.prime)) :
    b.comp (B.integralEmbedding iota) = j.localCharacter iota 1 := by
  ext a
  apply Subtype.coe_injective
  exact (RingHom.congr_fun hgeneric (B.integralEmbedding iota a)).trans
    ((congrArg η (B.integralEmbedding_toField iota a)).trans
      ((RingHom.congr_fun hfield (iota (a : E))).trans
        (RingHom.congr_fun j.integral_compatibility
          (NumberField.RingOfIntegers.mapRingHom iota a)).symm))

theorem coefficientResidueSquare_of_integral_map (b : B.R →+* ℤ_[q])
    (hcoeff : b.comp (B.integralEmbedding iota) = j.localCharacter iota 1)
    (hres : D.residue = PadicInt.toZMod.comp b) : ModelBlockCharacters.OrdinaryCharacterIntrinsic.CoefficientResidueSquare D j := by
  have hc : PadicInt.toZMod = (BlockCharacters.OrdinaryCharacterIntrinsic.blockResidueCast (k := ZMod q) (q := q)).comp
      (PadicInt.toZModPow 1) := padic_residue_hom_unique _ _
  apply RingHom.ext
  intro a
  exact (RingHom.congr_fun hres (B.integralEmbedding iota a)).trans
    ((congrArg PadicInt.toZMod (RingHom.congr_fun hcoeff a)).trans
      (RingHom.congr_fun hc (j.localCharacter iota 1 a)))

theorem coefficientResidueSquare_of_completion (b : B.R →+* ℤ_[q])
    (η : B.extension.carrier →+* ℚ_[q])
    (hgeneric : PadicInt.Coe.ringHom.comp b = η.comp B.toField)
    (hfield : η.comp (algebraMap K B.extension.carrier) =
      j.completion.toRingHom.comp (NumberField.FinitePlace.embedding j.prime))
    (hres : D.residue = PadicInt.toZMod.comp b) : ModelBlockCharacters.OrdinaryCharacterIntrinsic.CoefficientResidueSquare D j :=
  coefficientResidueSquare_of_integral_map D j b
    (completion_map_on_coefficients j b η hgeneric hfield) hres

end

end OAI.RepresentationTheory.Hecke.CoefficientResidueSquare.OrdinaryCharacterIntrinsic
