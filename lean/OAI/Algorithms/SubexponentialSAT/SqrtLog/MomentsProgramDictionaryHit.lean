import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramDictionaryNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramDictionaryMoves

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def hitBudget (p t : ℕ) (pairs : List (Word (baseWidth p t) × Word (baseWidth p t))) : ℕ :=
  9 * (RingScan.rightBits pairs).length + 7 * (RingScan.leftBits pairs).length +
  7 * pairs.length + pairs.length * (6000 * (baseWidth p t + 1)^2 + 34 * baseWidth p t + 29) + 23

theorem onHit_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (a : Tape)
    (hm : a.modulus = M.bits) (hnew : a.coeff = RingScan.leftBits pairs)
    (hf : a.found = Encoding.frame (RingScan.rightBits pairs))
    (hl : a.left = []) (hr : a.right = []) (ho : a.out = []) (hs : a.steps = [])
    (hc : a.count.length = pairs.length) (hw : a.width.length = baseWidth p t) :
    ∃ n ≤ hitBudget p t pairs, ∃ rr,
      Eval onHit n (machine regs a)
        (machine rr { a with found := [], left := [], right := [], steps := [], out := RingScan.sumBits p t M pairs }) := by
  obtain ⟨r1,hp⟩ := parseOld_eval regs a (RingScan.rightBits pairs) hf hl
  let a1 : Tape := { a with found := [], left := (RingScan.rightBits pairs).reverse }
  let a2 : Tape := { a1 with left := [], right := a1.left.reverse }
  let a3 : Tape := { a2 with left := a2.coeff }
  let a4 : Tape := { a3 with steps := a3.count }
  have ht := transferOld_eval r1 a1 hr
  have hn := copyNew_eval (readRegs r1 0 1 none) a2 rfl
  have hk := copyCount_eval (readRegs (readRegs r1 0 1 none) 0 1 none) a3 hs
  obtain ⟨n,nb,r5,ha⟩ := add_eval p t M pairs
    (readRegs (readRegs (readRegs r1 0 1 none) 0 1 none) 0 1 none) a4
    hm hnew (by simp [a4,a3,a2,a1]) ho hc hw
  have run := hp.seq (ht.seq (hn.seq (hk.seq ha)))
  refine ⟨_, ?_, r5, (by simpa only [onHit,a1,a2,a3,a4] using run)⟩
  dsimp [hitBudget]
  simp only [List.length_reverse,hnew,hc] at nb ⊢
  omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
