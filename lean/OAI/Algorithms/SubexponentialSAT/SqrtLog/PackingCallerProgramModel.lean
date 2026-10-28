import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramSelect
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramIncidence
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramSuffix
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputAddress

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

structure Problem where
  scopes : List (List ℕ)
  n : ℕ
  mask : List Bool
  mask_le : mask.length ≤ n
  r : ℕ
  Q : ℕ
  s : ℕ
  hr : 0 < r
  hQ : 0 < Q
  hs : 0 < s

namespace Problem

abbrev factors (p : Problem) := Semantics.factorCount p.scopes p.mask
abbrev incidences (p : Problem) := (Semantics.nativeEntries p.scopes p.mask).length
def raw (p : Problem) := PackingProgram.Assembly.Scope.raw p.scopes p.n p.mask
def words (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  (PackingProgram.Assembly.Scope.values p.scopes p.n p.mask p.mask_le a tail p.s p.hs p.hr).reverse

theorem words_length (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (p.words a tail).length=p.n+p.factors := by
  have h := PackingProgram.Assembly.Scope.rows_length p.scopes p.n p.mask p.mask_le
    a tail p.s p.hs p.hr
  simpa [words,factors,PackingProgram.Assembly.Scope.rows] using h

noncomputable def spec (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    LayoutProgram.NativePacking.Spec (UniversalType p.r p.Q 1) :=
  LayoutProgram.NativePacking.addressSpec p.hr p.hQ (p.words a tail)
    (Address.address p.scopes p.n p.mask p.mask_le (p.words a tail) (p.words_length a tail))

@[simp] theorem spec_dimension (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (p.spec a tail).params.D=p.incidences := rfl
@[simp] theorem spec_depth (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (p.spec a tail).params.Δ=1 := rfl
@[simp] theorem spec_width (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (p.spec a tail).params.width=List.replicate (p.Q*p.r) true := rfl
@[simp] theorem spec_alphabet (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (p.spec a tail).params.alphabet=AssignmentAlphabetSemantics.wordBytes p.r p.Q := rfl
@[simp] theorem spec_rows (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (p.spec a tail).params.rows=(p.words a tail).map ReadPlan.encodeWord := rfl

theorem spec_plans (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (p.spec a tail).params.planStream=planBits p.scopes p.n p.mask :=
  Address.planBytes_eq p.scopes p.n p.mask p.mask_le (p.words a tail) (p.words_length a tail)

end Problem

structure Parameters (outside : Store) (p : Problem) : Prop where
  ambient : SubexponentialSAT.BinaryArithmetic.toNat (outside 56)=p.n
  radius : SubexponentialSAT.BinaryArithmetic.toNat (outside 59)=p.r
  coordinate : SubexponentialSAT.BinaryArithmetic.toNat (outside 55)=p.Q
  epsilon : SubexponentialSAT.BinaryArithmetic.toNat (outside 57)=p.s
  incidence : SubexponentialSAT.BinaryArithmetic.toNat (outside 58)=p.incidences

structure Workspace (outside : Store) : Prop where
  temp : outside 52=[]
  width : outside 53=[]
  alphabet : outside 54=[]
  scopes : outside 60=[]
  plans : outside 61=[]
  words : outside 62=[]
  metadata : outside 63=[]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
