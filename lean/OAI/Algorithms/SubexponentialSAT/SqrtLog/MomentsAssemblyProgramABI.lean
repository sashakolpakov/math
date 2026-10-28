import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramFrames

namespace OAI.Algorithms

/-! The assembly input contains actual assignment lists and reusable metadata,
never head sums or products. The assignment worker consumes one ambient-order
assignment on stack 174 and produces its physical weight/jet on stacks 44/41.
The worker has the current support, head, and bucket contexts available. -/
namespace SubexponentialSAT.SqrtLog.MomentsAssembly

structure HeadInput where
  mask : List Bool
  context : List Bool
  assignments : List (List Bool)

structure BucketInput where
  context : List Bool
  heads : List HeadInput

def HeadInput.bits (h : HeadInput) : List Bool :=
  Encoding.frame h.mask ++ Encoding.frame h.context ++
    Encoding.frame (rawFrames h.assignments)

def BucketInput.bits (b : BucketInput) : List Bool :=
  Encoding.frame b.context ++ Encoding.frame (rawFrames (b.heads.map HeadInput.bits))

def bucketsInput (bs : List BucketInput) : List Bool :=
  rawFrames (bs.map BucketInput.bits)

def supportsInput (supports : List (List Bool)) : List Bool := rawFrames supports

/-
Fixed high-stack ABI:
160 current assignment stream; 161 current head stream;
162 current support stream; 163 bucket stream;
164 reversal buffer; 166 total sparse moment sum; 167 literal-one dictionary;
168 current support mask; 169 reusable support-list master;
170 reusable head-list master for this bucket;
174 current ambient assignment; 175 head context; 176 parser payload;
177 bucket context; 178 current head-membership mask; 179 copy buffer.
180..188 are exact-support projection scratch, empty between supports.
The Product core remains at 0..55, with head product40 and head sum42.
The ambient source cache128..137 is outside every assembly subroutine map.
-/

end SubexponentialSAT.SqrtLog.MomentsAssembly


end OAI.Algorithms
