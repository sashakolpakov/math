import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramMachine
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramMemory
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramStored

namespace OAI.Algorithms

/-! Native sparse arithmetic services shared by multiplier construction and Horner evaluation. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

structure Context (p t n d : ℕ) where
  modulus : SubexpPreparedQuartic.Modulus p t
  cache : RingProgram.ScalarCache p t
  zeroBound : BinaryArithmetic.toNat cache.zero.val < p^t
  table : Fin d → Fin d → Fin d → Word (baseWidth p t)
  u : ℕ
  J : ℕ
  width : List Bool
  widthLength : width.length=baseWidth p t

variable {p t n d : ℕ} [Fact p.Prime]

abbrev Data := Fin 40 → List Bool
abbrev Regs := Fin 8 → Bool
abbrev Raw := List (Product.Entry n (baseWidth p t) d)

def low (c : Context p t n d) : Fin 56 → List Bool :=
  Product.tapes (Product.idle c.modulus.bits c.width c.cache.zero.val
    (RingTriple.tableEncoding c.table) (List.replicate d true)
    (List.replicate c.u true) (List.replicate c.J true))

def constant (c : Context p t n d) (w : RingProgram.ScalarCode p t) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  constantStored p t c.cache w

def mul (c : Context p t n d) (a b : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  mulStored p t c.modulus c.cache c.table c.u c.J a b

def plus (c : Context p t n d) (a b : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  addStored p t c.modulus c.cache a b

def mulCost (c : Context p t n d) (a b : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : ℕ :=
  9*(Product.bytes a).length+11*(Product.bytes b).length+
    9*(Product.bytes (mul c a b)).length+
    Product.work p t c.modulus c.cache c.table c.u c.J a b []+29

def addCost (c : Context p t n d) (a b : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : ℕ :=
  18*(Product.bytes a).length+9*(Product.bytes b).length+
    9*(Product.bytes (plus c a b)).length+9*d+
    Normalize.work p t c.modulus c.cache Squarefree.encodeIndex a b+43

theorem mul_eval (c : Context p t n d) (a b : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (regs : Regs) (high : Data) (ha : high 11=Product.bytes a)
    (hb : high 5=Product.bytes b) (htmp : high 14=[]) :
    ∃ cost ≤ mulCost c a b, ∃ rr,
      Eval (productAdapter product) cost (Memory.state regs (low c) high)
        (Memory.state rr (low c) (binaryResult high (Product.bytes (mul c a b)))) := by
  exact ProductCallback.eval p t c.modulus c.cache c.zeroBound c.table
    (List.replicate d true) c.width (by simp) c.widthLength c.u c.J a b regs high ha hb htmp

theorem add_eval (c : Context p t n d) (a b : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (regs : Regs) (high : Data) (ha : high 11=Product.bytes a)
    (hb : high 5=Product.bytes b) (htmp : high 14=[]) :
    ∃ cost ≤ addCost c a b, ∃ rr,
      Eval add cost (Memory.state regs (low c) high)
        (Memory.state rr (low c) (binaryResult high (Product.bytes (plus c a b)))) := by
  simpa only [addCost, low, plus, addStored, Product.bytes, List.length_replicate] using
    IdempotentApplyProgram.add_eval p t c.modulus c.cache Squarefree.encodeIndex
      Squarefree.encodeIndex_injective (RingTriple.tableEncoding c.table)
      (List.replicate d true) c.width (List.replicate c.u true) (List.replicate c.J true)
      (by simp) c.widthLength a b regs high ha hb htmp


end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

end OAI.Algorithms
