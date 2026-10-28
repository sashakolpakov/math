import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAdd
import OAI.Algorithms.SubexponentialSAT.SubexpScalarLiteralProgram
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentSerialization

namespace OAI.Algorithms

/-! Exact byte and polynomial interpretations of the scalar literal emitted
after a weight run. No canonical representative is assumed for the output
word of the modular arithmetic program. -/

namespace SubexponentialSAT.SubexpWeightLiteralSemantics

open SubexpLiftRing SubexpQuarticRing

def constantCoefficient (p μ : ℕ) (output : List Bool)
    (houtput : output.length = baseWidth p μ) : Quad (Word (baseWidth p μ)) :=
  ⟨⟨output,houtput⟩,SubexpPreparedQuartic.zeroWord p μ,
    SubexpPreparedQuartic.zeroWord p μ,SubexpPreparedQuartic.zeroWord p μ⟩

def constantRaw (D p μ : ℕ) (output : List Bool)
    (houtput : output.length = baseWidth p μ) :
    SymbolicCost.CoeffList D (Quad (Word (baseWidth p μ))) :=
  [(SubexpArgumentCode.constantIndex D 0 0,constantCoefficient p μ output houtput)]

theorem serialized_constantRaw (D p μ : ℕ) [Fact p.Prime]
    (output shape : List Bool) (houtput : output.length = baseWidth p μ)
    (hshape : shape.length = baseWidth p μ) :
    SubexpScalarLiteralProgram.rawLiteral D (SubexpQuarticMarshal.marshalBits output shape) =
      Encoding.encodeList (SubexpArgumentEmitLoop.serializeTerm SubexpFlatAdd.encode)
        (constantRaw D p μ output houtput) := by
  rw [SubexpFlatAdd.marshalBits_eq_encode_constant p μ output shape houtput hshape]
  rfl

theorem denote_singleton_constant {R : Type*} [CommRing R] (D : ℕ) (c : R) :
    SymbolicCost.denote [(SubexpArgumentCode.constantIndex D 0 0,c)] =
      WeightedSupport.scalarHom (ι := Fin D) c := by
  simp [SymbolicCost.denote,SubexpArgumentCode.monomial_constantIndex,
    Polynomial.monomial_zero_left,WeightedSupport.scalarHom]

theorem denote_constantRaw (D p μ : ℕ) [Fact p.Prime]
    (c : Fin 4 → ZMod (p^μ)) (output : List Bool)
    (houtput : output.length = baseWidth p μ) :
    SymbolicCost.denote ((constantRaw D p μ output houtput).map
      (fun term => (term.1,quotientDenote c (term.2.map (wordValue p μ))))) =
      WeightedSupport.scalarHom (ι := Fin D)
        (LiftRing.of (QuarticSearch.poly c) (BinaryArithmetic.toNat output : ZMod (p^μ))) := by
  change SymbolicCost.denote [(SubexpArgumentCode.constantIndex D 0 0,
    quotientDenote c ((constantCoefficient p μ output houtput).map (wordValue p μ)))] = _
  rw [denote_singleton_constant]
  congr 1
  exact SubexpFlatAdd.encoded_constant_quotient p μ c output houtput

/-- The local residue equality supplied by the actual weight machine is
enough to identify the emitted raw polynomial with its lifted scalar weight. -/
theorem denote_weightRaw (D p μ : ℕ) [Fact p.Prime]
    (c : Fin 4 → ZMod (p^μ)) (output : List Bool)
    (houtput : output.length = baseWidth p μ) (weight : ZMod (p^μ))
    (hweight : (BinaryArithmetic.toNat output : ZMod (p^μ)) = weight) :
    SymbolicCost.denote ((constantRaw D p μ output houtput).map
      (fun term => (term.1,quotientDenote c (term.2.map (wordValue p μ))))) =
      WeightedSupport.scalarHom (ι := Fin D) (LiftRing.of (QuarticSearch.poly c) weight) := by
  rw [denote_constantRaw,hweight]

end SubexponentialSAT.SubexpWeightLiteralSemantics

end OAI.Algorithms
