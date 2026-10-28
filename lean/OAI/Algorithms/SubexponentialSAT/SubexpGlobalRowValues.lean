import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawRowTables
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowAssemblyPrepared
import OAI.Algorithms.SubexponentialSAT.SubexpRowToTaylorCalls

namespace OAI.Algorithms

/-! Typed values of the row bytes generated from the actual matrix and
cache tables. This is a representation of the computed row, not an input
row list. The machine still executes every matrix, mismatch and row loop. -/

namespace SubexponentialSAT.SubexpGlobalRowValues

open SubexpLiftRing SubexpQuarticRing

variable {p r Q Δ : ℕ} [Fact p.Prime]
variable (source : SubexpSelectedConversions.Prepared p 0) (i : Fin Δ)
  (u y : MulticolorTypes.UniversalType r Q Δ) (xs : List (ZMod p))
  (inverse negative : Fin Q → List Bool) (difference : Fin Q → Fin Q → List Bool)

def rawRow : Subexp.UniversalRowProgram.Row (List Bool) :=
  Subexp.UniversalRowDataProgram.row
    (Subexp.UniversalRowAssembly.computedTables p i u y xs inverse negative difference)
    (Subexp.UniversalRowAssembly.selected i u y)
    (if u = y then SubexpFlatAdd.encode source.one else SubexpFlatAdd.encode source.zero)
    (List.replicate xs.length true)

def expression : Algorithm.Expr (List (SubexpRowPolynomialCalls.Coefficient p 1)) :=
  SubexpRowExpression.expression source
    (SubexpRawRow.typedRow (baseWidth p 1) (rawRow source i u y xs inverse negative difference))

def output (μ : ℕ) : List Bool :=
  SubexpRowToTaylorCalls.output μ source xs.length (expression source i u y xs inverse negative difference)

theorem rawRow_valid
    (hi : ∀ j, (inverse j).length = 4 * baseWidth p 1)
    (hn : ∀ j, (negative j).length = 4 * baseWidth p 1)
    (hd : ∀ j k, (difference j k).length = 4 * baseWidth p 1) :
    SubexpRawRow.ValidRow (baseWidth p 1) (rawRow source i u y xs inverse negative difference) := by
  have hv := Subexp.UniversalRowAssembly.computedTables_valid p i u y xs inverse negative difference
    (SubexpFlatAdd.encode source.zero) (List.replicate (Q * (4 * baseWidth p 1)) false)
    (SubexpFlatAdd.encode_length source.zero)
    (by simp [Subexp.MatrixWordEncoding.width]) hi hn hd
  apply SubexpRawRow.valid_dataRow (baseWidth p 1) _ _ _ _ _ _ hv
    (SubexpFlatAdd.encode_length source.zero)
  split_ifs <;> exact SubexpFlatAdd.encode_length _

/-- The exact emitted postfix source is the serialization accepted by
the typed evaluator, including noncanonical but fixed-width cache words. -/
theorem sourceWord_eq_code
    (hi : ∀ j, (inverse j).length = 4 * baseWidth p 1)
    (hn : ∀ j, (negative j).length = 4 * baseWidth p 1)
    (hd : ∀ j k, (difference j k).length = 4 * baseWidth p 1)
    (a : Subexp.UniversalRowAssembly.Data)
    (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one) :
    Subexp.UniversalRowAssembly.sourceWord p i u y xs
      (Subexp.UniversalRowAssembly.computedTables p i u y xs inverse negative difference) a =
      SubexpRowToTaylorCalls.code (expression source i u y xs inverse negative difference) := by
  unfold Subexp.UniversalRowAssembly.sourceWord Subexp.UniversalRowAssembly.deltaWord
  rw [hzero, hone]
  exact SubexpRawRow.rowCode_eq_serialize source
    (rawRow source i u y xs inverse negative difference)
    (rawRow_valid source i u y xs inverse negative difference hi hn hd)

theorem expression_denote :
    ((expression source i u y xs inverse negative difference).map
      (SubexpRowSourceSemantics.denote source)).eval =
    (Subexp.UniversalRowProgram.rowExpression Polynomial.X
      (Subexp.UniversalRowProgram.mapRow
        (fun bits => Polynomial.C (SubexpRawRow.scalarDecode source bits))
        (rawRow source i u y xs inverse negative difference))).eval :=
  SubexpRawRow.expression_denote source (rawRow source i u y xs inverse negative difference)

theorem output_length (μ : ℕ) :
    (output source i u y xs inverse negative difference μ).length =
      (xs.length + 1) * (4 * baseWidth p μ) :=
  SubexpRowToTaylorCalls.output_length μ source xs.length
    (expression source i u y xs inverse negative difference)

end SubexponentialSAT.SubexpGlobalRowValues

end OAI.Algorithms
