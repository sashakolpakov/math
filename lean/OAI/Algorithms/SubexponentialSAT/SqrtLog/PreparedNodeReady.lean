import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReadyClean
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReadyNumeric
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeAddressedQuery

namespace OAI.Algorithms

/-! All literal node head inputs follow from executed query preparation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
open LeafHeadSetupProgram
attribute [local simp] Fin.coe_ofNat_eq_mod
variable {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data} {hg : Guard (q.input k)}
  {W V L : ℕ} (p : Query.Preparation q k a hg W V L)

 theorem parked (node : Fin (Query.packingProblem q k hg).Q) :
    Parked (Native.queryInputsAddressed q k hg p.firstWord p.remainingWords node) p.out := by
  have h := frontend_scalars q k a p.front p.lengths p.bankWords p.frontOutput hg
  constructor
  · exact (parked_parameter p 0 (by decide) (by decide) (by decide)).trans h.1
  · exact (parked_parameter p 1 (by decide) (by decide) (by decide)).trans h.2.1
  · exact (parked_parameter p 2 (by decide) (by decide) (by decide)).trans h.2.2.1
  · exact (parked_parameter p 3 (by decide) (by decide) (by decide)).trans h.2.2.2.1
  · exact (parked_parameter p 4 (by decide) (by decide) (by decide)).trans h.2.2.2.2.1
  · exact parked_words p
  · exact (parked_parameter p 6 (by decide) (by decide) (by decide)).trans p.frontOutput.low
  · exact parked_metadata p
  · exact (parked_plans p).trans (Native.queryInputsAddressed_stream q k hg p.firstWord p.remainingWords node).symm
  · exact (parked_parameter p 10 (by decide) (by decide) (by decide)).trans h.2.2.2.2.2.1
  · exact (parked_parameter p 11 (by decide) (by decide) (by decide)).trans h.2.2.2.2.2.2.1
  · exact (parked_parameter p 12 (by decide) (by decide) (by decide)).trans h.2.2.2.2.2.2.2.1
  · exact (congrArg BinaryArithmetic.toNat (parked_parameter p 13 (by decide) (by decide) (by decide))).trans h.2.2.2.2.2.2.2.2

 theorem prepared_parked (node : Fin (Query.packingProblem q k hg).Q) :
    Parked (Native.queryInputsAddressed q k hg p.firstWord p.remainingWords node)
      (Marked.Wide.maskCopied (Query.prepared p.out)) :=
  parked_maskCopied (parked_prepared (parked p node))

 theorem prepared_blank_of_low (hb : NodeNative.Blank a)
    (hlow : ∀ i : Fin 768,i.val < 190 → p.packed.stacks i=[] → p.out.stacks i=[]) :
    NodeNative.Blank (Marked.Wide.maskCopied (Query.prepared p.out)) := by
  apply maskCopied_blank
  apply prepared_blank
  intro i hi hn h190 h191 h699
  have hregions := (Node.mem_cleanup i).mp hi
  by_cases hlo : i.val < 190
  · exact hlow i hlo (packed_low_blank p hb i hi hn hlo)
  have h190' : i.val≠190 := by intro he; apply h190; exact Fin.ext he
  have h191' : i.val≠191 := by intro he; apply h191; exact Fin.ext he
  exact out_high_blank p hb i hi (by omega) h699
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady

end

end OAI.Algorithms
