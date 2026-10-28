import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgramAuxiliary
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtractionOuter
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingLeftovers
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange

namespace OAI.Algorithms

/-! The fixed physical packing controller. Every alphabet, bucket, selected
vertex, leftover, and inverse-address query is produced by actual programs. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

def extractionSave : List Op := PackingPlumbing.move 10 30 39 ++
  [.clear 15, .copy 13 6 39]
def verticesSetup : List Op := [.copy 42 0 39]
def verticesSave : List Op := PackingPlumbing.move 5 7 39
def leftoversSave : List Op := PackingPlumbing.move 10 31 39 ++
  PackingPlumbing.move 13 32 39 ++ PackingPlumbing.move 14 33 39 ++
  [.push 12 false, .transfer 12 34, .clear 6, .clear 11]
abbrev extractionCall : Cmd 16 48 := lowCall PackingExtraction.program (by decide) (by decide)
abbrev verticesCall : Cmd 16 48 := lowCall AssignmentSeedRange.program (by decide) (by decide)
abbrev leftoversCall : Cmd 16 48 := lowCall PackingLeftovers.program (by decide) (by decide)
abbrev extraction : Cmd 16 48 := .seq extractionCall (PackingPlumbing.command extractionSave)
abbrev vertices : Cmd 16 48 := .seq (PackingPlumbing.command verticesSetup)
  (.seq verticesCall (PackingPlumbing.command verticesSave))
abbrev leftovers : Cmd 16 48 := .seq leftoversCall (PackingPlumbing.command leftoversSave)
abbrev packing : Cmd 16 48 := sequence [buckets, extraction, vertices, leftovers, inverse]
abbrev command : Cmd 16 48 := .seq frontend packing

/-- Input40 is the actual assignment. Output32 is the complete physical
metadata table; output35 is the inverse read plan in original vertex order. -/
def program := compiled command 40 32

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
