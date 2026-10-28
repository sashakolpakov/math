import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketData
import OAI.Algorithms.SubexponentialSAT.SubexpBlueprintExecution
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceSemantics

namespace OAI.Algorithms

/-! Local provenance for the factor packets produced by the actual blueprint
controller. The constructed witness retains the exact emitted byte order. -/

namespace SubexponentialSAT.SubexpFactorPacketProvenance

open SubexpLiftRing SubexpQuarticRing SubexpSymbolicCost
open SubexpSelectedConversions SubexpInputBitProgram

variable {p D labels arity degree : ℕ} [Fact p.Prime]
variable (source : Prepared p 0) (target : Prepared p D)
variable (theta : Code p D)
variable (minusOne : Word (baseWidth p (D+1))) (point : Fin D → ResidueCode p)
variable (input : Input p D labels arity degree)

def coordinate (row : SubexpTableInterpolation.Row labels arity (Code p D))
    (i : Fin arity) : SubexpBlueprintCoordinate.Coordinate p D where
  origin := input.origins i
  columns := columns source target theta input i
  dimension := by rw [columns_eq]; simp
  coefficients := (input.cache.getD (row.labels.get i).val []).map SubexpQuarticFlatNeg.flat

def blueprintRows : List (SubexpBlueprintRows.Row p D) :=
  input.rows.map fun row =>
    ⟨SubexpQuarticFlatNeg.flat row.value,
      List.ofFn (coordinate source target theta input row)⟩

theorem argument_bytes (ctx : SubexpBlueprintFactor.Context)
    (hindex : ctx.indexWidth = SubexpSymbolicCost.indexBits D)
    (row : SubexpTableInterpolation.Row labels arity (Code p D)) (i : Fin arity) :
    SubexpDenseSerialization.encodeFixedQuarticCoefficients p D
        (argument source target theta minusOne point input i) =
      SubexpBlueprintCoordinate.argument ctx source target minusOne point
        (coordinate source target theta input row i) := by
  change SubexpDenseSerialization.encodeFixedQuarticCoefficients p D
      (argument source target theta minusOne point input i) =
    SubexpCacheArgument.resultBits
      (SubexpQuarticFlatNeg.flat (betaOutput source (input.origins i) point))
      (SubexpQuarticFlatNeg.flat
        (SubexpQuarticNegMachine.negateWords p (D+1) target.modulus minusOne
          (betaOutput source (input.origins i) point)))
      (columns source target theta input i) ctx.indexWidth [false]
  rw [columns_eq, hindex, SubexpCacheArgument.resultBits_compileColumns]
  exact (serialize_raw (argument source target theta minusOne point input i)).symm

/-- The typing witness describes precisely the prepared rows emitted by the
blueprint program, including the actual reverse order of its Ce terms. -/
theorem factor_prepared (ctx : SubexpBlueprintFactor.Context)
    (hdimension : ctx.dimension = D)
    (hindex : ctx.indexWidth = SubexpSymbolicCost.indexBits D) :
    (factor source target theta minusOne point input).prepared
        (SubexpDenseSerialization.encodeFixedQuarticCoefficients p D)
        (SubexpWeightCode.rawScalar D) =
      SubexpBlueprintExecution.preparedRows ctx source target minusOne point
        (blueprintRows source target theta input) := by
  unfold SubexpBlockAssemblySemantics.Factor.prepared factor
    SubexpBlueprintExecution.preparedRows SubexpPreparedFactor.prepareRows
    SubexpBlueprintRows.rowsOutput blueprintRows
  rw [hdimension]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro row hrow
  change SubexpTableSource.Row.mk _ _ = SubexpTableSource.Row.mk _ _
  congr 1
  · exact scalar_bytes row.value
  · simp only [SubexpBlueprintRows.output, List.map_ofFn, Function.comp_def]
    apply congrArg List.ofFn
    funext i
    change SubexpTableSource.Coordinate.mk _ _ = SubexpTableSource.Coordinate.mk _ _
    congr 1
    · exact argument_bytes source target theta minusOne point input ctx hindex row i
    · simp only [coordinate, SubexpBlueprintCoordinate.output, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro a ha
      exact scalar_bytes a

theorem factor_exists (ctx : SubexpBlueprintFactor.Context)
    (hdimension : ctx.dimension = D)
    (hindex : ctx.indexWidth = SubexpSymbolicCost.indexBits D) :
    ∃ f : SubexpBlockAssemblySemantics.Factor (Code p D) (Raw p D),
      f.prepared (SubexpDenseSerialization.encodeFixedQuarticCoefficients p D)
          (SubexpWeightCode.rawScalar D) =
        SubexpBlueprintExecution.preparedRows ctx source target minusOne point
          (blueprintRows source target theta input) :=
  ⟨factor source target theta minusOne point input,
    factor_prepared source target theta minusOne point input ctx hdimension hindex⟩

/-- The actual blueprint instruction table produces the prepared form of
the constructed typed factor. No source bytes or Ce literals are inputs. -/
theorem program_runs_typed (ctx : SubexpBlueprintFactor.Context)
    (hc : SubexpBlueprintCoordinate.ContextGood ctx source target minusOne point)
    (hindex : ctx.indexWidth = SubexpSymbolicCost.indexBits ctx.dimension)
    (regs : Fin 8 → Bool) :
    BitProgram.RunsIn SubexpBlueprintFactor.program
      (SubexpBlueprintExecution.runCost ctx source target minusOne point
        (blueprintRows source target theta input))
      ((SubexpBlueprintFactor.serviceState ctx regs
        (Subexp.FactorBlueprint.encodeRows
          ((blueprintRows source target theta input).map SubexpBlueprintRows.Row.packet))).withPC
        (some SubexpBlueprintFactor.program.entry))
      ((SubexpBlueprintFactor.serviceState ctx (fun _ => false)
        (SubexpTableSource.encodeRows
          ((factor source target theta minusOne point input).prepared
            (SubexpDenseSerialization.encodeFixedQuarticCoefficients p D)
            (SubexpWeightCode.rawScalar D)))).withPC none) := by
  have h := SubexpBlueprintExecution.program_runsIn ctx source target minusOne point hc hindex
    (blueprintRows source target theta input) regs
  rw [← factor_prepared source target theta minusOne point input ctx hc.dimension
    (hindex.trans (congrArg SubexpSymbolicCost.indexBits hc.dimension))] at h
  exact h

/-- The local row identity lifts directly to the typing condition consumed
by the actual moment-source proof. The remaining equality only identifies
the ordered physical factor packets stored in this term. -/
theorem term_factorsTyped {mctx : SubexpMomentSourceProgram.Context}
    {a : Fin mctx.dimension → ℕ} (term : SubexpMomentSourceProgram.TermResult mctx a)
    (sourceData : Prepared p 0) (targetData : Prepared p mctx.dimension)
    (thetaData : Code p mctx.dimension)
    (minusOneData : Word (baseWidth p (mctx.dimension+1)))
    (pointData : Fin mctx.dimension → ResidueCode p)
    (ctx : SubexpBlueprintFactor.Context) (hdimension : ctx.dimension = mctx.dimension)
    (hindex : ctx.indexWidth = SubexpSymbolicCost.indexBits mctx.dimension)
    (packets : List (Packet p mctx.dimension))
    (hpackets : term.input.factors = packets.map (fun packet =>
      SubexpBlueprintExecution.preparedRows ctx sourceData targetData minusOneData pointData
        (blueprintRows sourceData targetData thetaData packet.input))) :
    SubexpMomentSourceSemantics.FactorsTyped (p := p) term := by
  refine ⟨packets.map (fun packet =>
    factor sourceData targetData thetaData minusOneData pointData packet.input), ?_⟩
  rw [hpackets, List.map_map]
  apply List.map_congr_left
  intro packet hpacket
  exact factor_prepared sourceData targetData thetaData minusOneData pointData packet.input
    ctx hdimension hindex

end SubexponentialSAT.SubexpFactorPacketProvenance

end OAI.Algorithms
