import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawQuartic
import OAI.Algorithms.SubexponentialSAT.SubexpRowExpression

namespace OAI.Algorithms

/-! Give the raw universal-row emitter a typed dense-literal interpretation.
All assumptions are individual payload lengths. The original bytes, including
noncanonical residue representatives, are retained exactly. -/

namespace SubexponentialSAT.SubexpRawRow

open SubexpLiftRing SubexpQuarticRing
open Subexp.UniversalRowProgram

structure ValidFactor (B : ℕ) (factor : Factor (List Bool)) : Prop where
  inverseDifference : factor.inverseDifference.length = 4 * B
  negativeNode : factor.negativeNode.length = 4 * B

structure ValidTerm (B : ℕ) (term : Term (List Bool)) : Prop where
  value : term.value.length = 4 * B
  inverseNode : term.inverseNode.length = 4 * B
  factors : ∀ f ∈ term.factors, ValidFactor B f

structure ValidRow (B : ℕ) (row : Row (List Bool)) : Prop where
  delta : row.delta.length = 4 * B
  terms : ∀ t ∈ row.terms, ValidTerm B t

def typedRow (B : ℕ) (row : Row (List Bool)) : Row (Quad (Word B)) :=
  mapRow (SubexpRawQuartic.ofBits B) row

theorem factor_roundtrip (B : ℕ) (factor : Factor (List Bool)) (h : ValidFactor B factor) :
    mapFactor SubexpFlatAdd.encode (mapFactor (SubexpRawQuartic.ofBits B) factor) = factor := by
  cases factor with
  | mk inverseDifference negativeNode =>
      simp only [mapFactor, SubexpRawQuartic.encode_ofBits B _ h.inverseDifference,
        SubexpRawQuartic.encode_ofBits B _ h.negativeNode]

theorem term_roundtrip (B : ℕ) (term : Term (List Bool)) (h : ValidTerm B term) :
    mapTerm SubexpFlatAdd.encode (mapTerm (SubexpRawQuartic.ofBits B) term) = term := by
  have hf : (term.factors.map (mapFactor (SubexpRawQuartic.ofBits B))).map
      (mapFactor SubexpFlatAdd.encode) = term.factors := by
    rw [List.map_map]
    calc
      _ = term.factors.map id := by
        apply List.map_congr_left
        intro f hf
        exact factor_roundtrip B f (h.factors f hf)
      _ = _ := List.map_id _
  cases term with
  | mk value inverseNode factors =>
      simp only [mapTerm, SubexpRawQuartic.encode_ofBits B _ h.value,
        SubexpRawQuartic.encode_ofBits B _ h.inverseNode]
      exact congrArg (fun fs => Term.mk value inverseNode fs) hf

theorem row_roundtrip (B : ℕ) (row : Row (List Bool)) (h : ValidRow B row) :
    mapRow SubexpFlatAdd.encode (typedRow B row) = row := by
  have ht : (row.terms.map (mapTerm (SubexpRawQuartic.ofBits B))).map
      (mapTerm SubexpFlatAdd.encode) = row.terms := by
    rw [List.map_map]
    calc
      _ = row.terms.map id := by
        apply List.map_congr_left
        intro t ht
        exact term_roundtrip B t (h.terms t ht)
      _ = _ := List.map_id _
  cases row with
  | mk delta terms =>
      simp only [typedRow, mapRow, SubexpRawQuartic.encode_ofBits B _ h.delta]
      exact congrArg (fun ts => Row.mk delta ts) ht

private theorem mapRow_comp {A B C : Type*} (f : A → B) (g : B → C) (row : Row A) :
    mapRow g (mapRow f row) = mapRow (g ∘ f) row := by
  simp [mapRow, mapTerm, mapFactor, List.map_map, Function.comp_def]

variable {p : ℕ} [Fact p.Prime] (source : SubexpSelectedConversions.Prepared p 0)

/-- Exact code equality for the raw row already on the machine. -/
theorem rowCode_eq_serialize (row : Row (List Bool)) (h : ValidRow (baseWidth p 1) row) :
    rowCode (SubexpFlatAdd.encode source.zero) (SubexpFlatAdd.encode source.one)
        (SubexpFlatAdd.encode source.zero ++ SubexpFlatAdd.encode source.one) row =
      SubexpPostfixControl.serializeCode SubexpRowExpression.encode
        (SubexpRowExpression.expression source (typedRow (baseWidth p 1) row)).compile := by
  have he := SubexpRowExpression.rowCode_eq_serialize source (typedRow (baseWidth p 1) row)
  rw [row_roundtrip _ row h] at he
  exact he

/-- The semantic decoder acts on the existing raw representative. -/
noncomputable def scalarDecode (bits : List Bool) : SubexpActualRing.E p :=
  source.residueRing.decode (SubexpRawQuartic.ofBits (baseWidth p 1) bits)

theorem expression_denote (row : Row (List Bool)) :
    ((SubexpRowExpression.expression source (typedRow (baseWidth p 1) row)).map
      (SubexpRowSourceSemantics.denote source)).eval =
    (rowExpression Polynomial.X (mapRow (fun bits => Polynomial.C (scalarDecode source bits)) row)).eval := by
  rw [SubexpRowExpression.expression_denote]
  simp only [typedRow, mapRow_comp, Function.comp_def, scalarDecode]

end SubexponentialSAT.SubexpRawRow

end OAI.Algorithms
