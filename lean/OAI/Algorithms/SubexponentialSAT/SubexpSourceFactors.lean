import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSourceSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpRepresentedBuilder

namespace OAI.Algorithms

/-!
# Local meaning of physically prepared factor tables

The scalar table entries and Horner caches are decoded coefficientwise. The
argument literals need only have the proved polynomial denotations; their
stored term order and zero padding need not match the reference builder.
-/

namespace SubexponentialSAT.SubexpSourceFactors

open SubexpBlockAssemblySemantics
open SubexpSourceSemantics

private theorem map_map {A B C : Type*} (f : A → B) (g : B → C)
    (e : Algorithm.Expr A) :
    (e.map f).map g = e.map (fun x => g (f x)) := by
  induction e with
  | lit x => rfl
  | add a b ha hb => simp only [Algorithm.Expr.map, ha, hb]
  | mul a b ha hb => simp only [Algorithm.Expr.map, ha, hb]

variable {D : ℕ} {C R : Type*} [One C] [CommRing R]

local instance : Zero (SymbolicCost.CoeffList D C) := ⟨[]⟩
local instance : One (SymbolicCost.CoeffList D C) := ⟨SubexpAlgorithm.rawOne D⟩

/-- The value of a prepared factor follows from each cached interpolation
polynomial and each actual argument literal. No equality of whole factor
programs is assumed. -/
theorem factor_value (decode : C → R) (hone : decode 1 = 1)
    (f : Factor C (SymbolicCost.CoeffList D C))
    (labels : Fin f.labels → R) (hu : TableInterpolation.UnitDifferences labels)
    (hcache : ∀ i : Fin f.labels,
      PolynomialAlgorithm.denote ((f.cache.map (List.map decode)).getD i.val []) =
        TableInterpolation.basis labels hu i) :
    ((f.expression (SubexpWeightCode.rawScalar D)).map
      (fun raw => SymbolicCost.denote (decodeRaw decode raw))).eval =
      MvPolynomial.eval₂ WeightedSupport.scalarHom
        (fun i => SymbolicCost.denote (decodeRaw decode (f.inputs i)))
        (SubexpTableInterpolation.tablePolynomial labels hu
          (f.rows.map (SubexpRepresentedBuilder.mapRow decode))) := by
  let : Zero (SymbolicCost.CoeffList D R) := ⟨[]⟩
  let : One (SymbolicCost.CoeffList D R) := ⟨SubexpAlgorithm.rawOne D⟩
  rw [← map_map]
  change (((SubexpTableInterpolation.tableExpr (SubexpWeightCode.rawScalar D)
    f.cache f.rows (fun i => Algorithm.Expr.lit (f.inputs i))).map
      (SubexpRepresentedBuilder.mapRaw decode)).map SymbolicCost.denote).eval = _
  rw [SubexpRepresentedBuilder.map_tableExpr decode hone]
  rw [SubexpTableInterpolation.tableExpr_correct
    (R := R) (A := SymbolicCost.CoeffList D R) (S := SymbolicCost.Poly D R)
    (SubexpWeightCode.rawScalar D) SymbolicCost.denote WeightedSupport.scalarHom
    (by rfl) (SubexpAlgorithm.rawOne_denote D)
    (SubexpWeightCode.rawScalar_denote D) labels hu
    (f.cache.map (List.map decode)) hcache]
  rfl

/-- Reindex one actual factor to its scope in the input instance. The only
remaining facts are its table entries and the denotation of each emitted
argument, which are the outputs of the table and Taylor producers. -/
theorem factor_value_eq (decode : C → R) (hone : decode 1 = 1)
    (f : Factor C (SymbolicCost.CoeffList D C))
    (labels : Fin f.labels → R) (hu : TableInterpolation.UnitDifferences labels)
    (hcache : ∀ i : Fin f.labels,
      PolynomialAlgorithm.denote ((f.cache.map (List.map decode)).getD i.val []) =
        TableInterpolation.basis labels hu i)
    {σ : Type*} (ix : Fin f.arity ≃ σ) (table : MvPolynomial σ R)
    (argument : σ → SymbolicCost.Poly D R)
    (htable : SubexpTableInterpolation.tablePolynomial labels hu
      (f.rows.map (SubexpRepresentedBuilder.mapRow decode)) =
        MvPolynomial.rename ix.symm table)
    (hargument : ∀ i, SymbolicCost.denote (decodeRaw decode (f.inputs i)) =
      argument (ix i)) :
    ((f.expression (SubexpWeightCode.rawScalar D)).map
      (fun raw => SymbolicCost.denote (decodeRaw decode raw))).eval =
      MvPolynomial.eval₂ WeightedSupport.scalarHom argument table := by
  rw [factor_value decode hone f labels hu hcache, htable, MvPolynomial.eval₂_rename]
  congr 1
  funext i
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hargument (ix.symm i)

end SubexponentialSAT.SubexpSourceFactors

end OAI.Algorithms
