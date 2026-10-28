import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgramInput
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketExecution
import OAI.Algorithms.SubexponentialSAT.SubexpVertexIndexProgram

namespace OAI.Algorithms

/-! Independent fixed bucket and inverse-address stages. -/
namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

def bucketsSetup : List Op := PackingPlumbing.move 26 6 39 ++
  PackingPlumbing.move 27 7 39 ++ [.copy 42 10 39]
def bucketsSave : List Op := [.clear 6] ++ PackingPlumbing.move 5 15 39 ++
  PackingPlumbing.move 10 16 39
def queriesSetup : List Op := [.copy 42 0 39]
def queriesSave : List Op := PackingPlumbing.move 3 6 39 ++ [.clear 1, .copy 33 7 39]
def inverseSave : List Op := PackingPlumbing.move 8 35 39 ++ [.clear 7]

abbrev bucketsCall : Cmd 16 48 := lowCall PackingBucketTable.program (by decide) (by decide)
abbrev queriesCall : Cmd 16 48 := lowCall SubexpVertexIndexProgram.program (by decide) (by decide)
abbrev inverseCall : Cmd 16 48 := lowCall SelectorMapProgram.program (by decide) (by decide)

abbrev buckets : Cmd 16 48 := .seq (PackingPlumbing.command bucketsSetup)
  (.seq bucketsCall (PackingPlumbing.command bucketsSave))
abbrev inverse : Cmd 16 48 := .seq (PackingPlumbing.command queriesSetup)
  (.seq queriesCall (.seq (PackingPlumbing.command queriesSave)
    (.seq inverseCall (PackingPlumbing.command inverseSave))))


end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
