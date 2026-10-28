import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheState
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheIndex

namespace OAI.Algorithms

/-! The concrete inner cache callback: compare the loop positions, update
the two products off the diagonal, then increment the encoded integer. -/

namespace SubexponentialSAT.SubexpLagrangeCacheInner

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpLagrangeCacheWorkspace
open SubexpLagrangeCacheState

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

structure Environment (D : ℕ) (t zero one : Coefficient p μ)
    (minusOne : Word (baseWidth p μ)) (width : List Bool) (base : Store) (i : ℕ) : Prop where
  width_eq : width.length = baseWidth p μ
  workspace : Ready M.bits width (SubexpQuarticFlatMul.flat t) (baseWidth p μ) base
  zero_eq : SubexpFlatAdd.encode zero = List.replicate (4 * baseWidth p μ) false
  one_eq : base 207 = SubexpFlatAdd.encode one
  minus_eq : base 211 = minusOne.val
  theta_eq : base 213 = SubexpFlatAdd.encode zero
  index_eq : base 248 = List.replicate i false
  label_eq : base 217 = SubexpFlatAdd.encode (label p μ M zero one i)
  zero_array : base 242 = encode p μ (List.replicate D zero)
  dimension : base 243 = List.replicate D true
  empty : ∀ k ∈ ([214, 219, 236, 237, 238, 241, 244, 245] : List (Fin 256)), base k = []

def stepBound (D B i j : ℕ) : ℕ :=
  2100000 * (D + 1)^3 * (B + 1)^2 + 18 * i + 9 * j + 50

theorem step_eval (D : ℕ) (t zero one : Coefficient p μ)
    (minusOne : Word (baseWidth p μ)) (width : List Bool) (base : Store) (i j : ℕ)
    (H : Environment p μ M D t zero one minusOne width base i)
    (a : Partial p μ D) (todo : List Bool) (regs : Fin 16 → Bool) :
    ∃ n ≤ stepBound D (baseWidth p μ) i j, ∃ rf,
      Eval SubexpLagrangeCacheControl.innerStep n
        ⟨regs, view p μ M D base zero one j a todo⟩
        ⟨rf, view p μ M D base zero one (j + 1)
          (advance p μ M D t zero one minusOne i j a) todo⟩ := by
  let s := view p μ M D base zero one j a todo
  let next := advance p μ M D t zero one minusOne i j a
  let s1 := view p μ M D base zero one j next todo
  let B := baseWidth p μ
  have HS : Ready M.bits width (SubexpQuarticFlatMul.flat t) B s :=
    view_workspace p μ M D base t zero one width H.workspace j a todo
  have HS1 : Ready M.bits width (SubexpQuarticFlatMul.flat t) B s1 :=
    view_workspace p μ M D base t zero one width H.workspace j next todo
  have hempty (k : Fin 256)
      (hk : k ∈ ([214, 219, 236, 237, 238, 241, 244, 245] : List (Fin 256))) : s k = [] := by
    have h := H.empty k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [s, view] using h
  obtain ⟨nc, hnc, rc, hc, hflag⟩ := SubexpLagrangeCacheIndex.compare_unary
    (⟨regs, s⟩ : Data) i j
    (by simpa [s, view] using H.index_eq) (by simp [s, view])
    (HS 120 (by decide)) (hempty 236 (by simp)) (hempty 237 (by simp)) (hempty 238 (by simp))
  have hbranch : ∃ nb ≤ 2000000 * (D + 1)^3 * (B + 1)^2 + 1, ∃ rb,
      Eval (.ite 7 (.base .skip) SubexpLagrangeCacheControl.innerProduct) nb
        (⟨rc, s⟩ : Data) ⟨rb, s1⟩ := by
    by_cases hij : i = j
    · have hn : next = a := by simp [next, advance, hij]
      have hs : s1 = s := by simp only [s1, s, hn]
      refine ⟨1, by omega, rc, ?_⟩
      rw [hs]
      apply Eval.ite_true (by simpa [hij] using hflag)
      exact .base (.skip _)
    · have hprod := SubexpLagrangeCacheProduct.product_run p μ M s D t zero one
        a.denominator (label p μ M zero one i) (label p μ M zero one j)
        minusOne width H.width_eq HS H.zero_eq
        (by simp [s, view]) (by simpa [s, view] using H.one_eq)
        (by simpa [s, view] using H.minus_eq) (by simpa [s, view] using H.theta_eq)
        (by simpa [s, view] using H.label_eq) (by simp [s, view])
        a.polynomial a.length_eq (by rfl)
        (by simpa [s, view, SubexpLagrangeCacheState.encode,
          SubexpLagrangeCacheProduct.encode] using H.zero_array)
        (by simpa [s, view] using H.dimension)
        (hempty 214 (by simp)) (hempty 219 (by simp)) (hempty 241 (by simp))
        (hempty 244 (by simp)) (hempty 245 (by simp)) rc
      obtain ⟨np, rp, hnp, hp⟩ := hprod
      have hs : Function.update (Function.update s 205
          (SubexpFlatAdd.encode (SubexpLagrangeCacheProduct.denominator p μ M t minusOne
            a.denominator (label p μ M zero one i) (label p μ M zero one j)))) 240
          (SubexpLagrangeCacheProduct.encode p μ
            (SubexpLagrangeCacheProduct.polynomial p μ M t zero one minusOne
              (label p μ M zero one j) D a.polynomial)) = s1 := by
        simpa only [s, s1, next, advance, ite_eq_right hij,
          SubexpLagrangeCacheState.encode, SubexpLagrangeCacheProduct.encode] using
          view_partial p μ M D base zero one j a next todo
      rw [hs] at hp
      refine ⟨np + 1, by dsimp only [B]; omega, rp, ?_⟩
      exact Eval.ite_false (by simpa [hij] using hflag) hp
  obtain ⟨nb, hnb, rb, hb⟩ := hbranch
  have hadd := SubexpLagrangeScalarCalls.addTo_run p μ M s1 218 207 218
    (by decide) (by decide) (by decide) (by decide)
    (label p μ M zero one j) one width (fun _ => []) H.width_eq
    (by simp [s1, view]) (by simpa [s1, view] using H.one_eq) HS1.low
    (HS1 120 (by decide)) (by simpa [s1, view] using H.empty 245 (by simp)) rb
  obtain ⟨na, ra, hna, ha⟩ := hadd
  let s2 := Function.update s1 218 (SubexpFlatAdd.encode (label p μ M zero one (j + 1)))
  change Eval (SubexpLagrangeScalarCalls.addTo 218 207 218) na ⟨rb, s1⟩ ⟨ra, s2⟩ at ha
  have hindex : s2 249 = List.replicate j false := by simp [s2, s1, view]
  obtain ⟨ni, ri, hni, hi⟩ := appendIndex_run 249 s2 ra
  have hsnext : Function.update s2 249 (false :: s2 249) =
      view p μ M D base zero one (j + 1) next todo := by
    rw [hindex]
    exact view_next p μ M D base zero one j next todo
  rw [hsnext] at hi
  have he := hc.seq (hb.seq (ha.seq hi))
  refine ⟨nc + (nb + (na + ni)), ?_, ri, he⟩
  · have hlen : (s1 218).length = 4 * B := by
      simp [s1, view, SubexpFlatAdd.encode_length, B]
    rw [hlen] at hna
    unfold stepBound
    dsimp only [B] at hnb hna ⊢
    apply (Nat.add_le_add hnc (Nat.add_le_add hnb (Nat.add_le_add hna hni))).trans
    ring_nf
    omega

def loopBound (D B i j n : ℕ) : ℕ :=
  n * (2100000 * (D + 1)^3 * (B + 1)^2 + 18 * i + 9 * (j + n) + 52) + 2

theorem visits (D : ℕ) (t zero one : Coefficient p μ)
    (minusOne : Word (baseWidth p μ)) (width : List Bool) (base : Store) (i : ℕ)
    (H : Environment p μ M D t zero one minusOne width base i) (n : ℕ) :
    ∀ j (a : Partial p μ D) (regs : Fin 16 → Bool),
      ∃ costs ticks rf,
        UnaryForPrograms.Visits SubexpLagrangeCacheControl.innerCounter
          SubexpLagrangeCacheControl.innerStep costs ticks
          (⟨regs, view p μ M D base zero one j a (List.replicate n true)⟩ : Data)
          ⟨rf, view p μ M D base zero one (j + n)
            (run p μ M D t zero one minusOne i j n a) []⟩ ∧
        ticks ≤ loopBound D (baseWidth p μ) i j n := by
  induction n with
  | zero =>
      intro j a regs
      let d : Data := ⟨regs, view p μ M D base zero one j a []⟩
      let rf := readRegs regs 0 1 none
      have hp : UnaryForPrograms.popped SubexpLagrangeCacheControl.innerCounter d =
          (⟨rf, view p μ M D base zero one j a []⟩ : Data) := by
        apply SubexpScanPrimitives.state_ext
        · simp [UnaryForPrograms.popped, SubexpLagrangeCacheControl.innerCounter,
            d, view, rf]
        · simp [UnaryForPrograms.popped, SubexpLagrangeCacheControl.innerCounter,
            d, view, Function.update_idem]
      refine ⟨[], 2, rf, ?_, by simp [loopBound]⟩
      have hv := UnaryForPrograms.Visits.done
        (p := SubexpLagrangeCacheControl.innerCounter)
        (body := SubexpLagrangeCacheControl.innerStep) d (by simp [d, view,
          SubexpLagrangeCacheControl.innerCounter])
      simpa only [hp, d, run, Nat.add_zero, List.replicate_zero] using hv
  | succ n ih =>
      intro j a regs
      let d : Data := ⟨regs, view p μ M D base zero one j a (List.replicate (n + 1) true)⟩
      let rp := readRegs regs 0 1 (some true)
      let next := advance p μ M D t zero one minusOne i j a
      have hp : UnaryForPrograms.popped SubexpLagrangeCacheControl.innerCounter d =
          (⟨rp, view p μ M D base zero one j a (List.replicate n true)⟩ : Data) := by
        apply SubexpScanPrimitives.state_ext
        · simp [UnaryForPrograms.popped, SubexpLagrangeCacheControl.innerCounter,
            d, view, rp, List.replicate_succ]
        · simp [UnaryForPrograms.popped, SubexpLagrangeCacheControl.innerCounter,
            d, view, List.replicate_succ, Function.update_idem]
      obtain ⟨nb, hnb, rb, hb⟩ := step_eval p μ M D t zero one minusOne width base i j H
        a (List.replicate n true) rp
      obtain ⟨costs, nt, rt, ht, hnt⟩ := ih (j + 1) next rb
      have hstep : Eval SubexpLagrangeCacheControl.innerStep nb
          (UnaryForPrograms.popped SubexpLagrangeCacheControl.innerCounter d)
          (⟨rb, view p μ M D base zero one (j + 1) next (List.replicate n true)⟩ : Data) := by
        rw [hp]
        exact hb
      have hv := UnaryForPrograms.Visits.step
        (p := SubexpLagrangeCacheControl.innerCounter)
        (body := SubexpLagrangeCacheControl.innerStep) (d := d)
        (by simp [d, view, SubexpLagrangeCacheControl.innerCounter]) hstep
        (by rw [hp]; simp [view, SubexpLagrangeCacheControl.innerCounter]) ht
      refine ⟨nb :: costs, nb + nt + 2, rt, ?_, ?_⟩
      · simpa only [d, next, run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv
      · let K := 2100000 * (D + 1)^3 * (baseWidth p μ + 1)^2 +
          18 * i + 9 * (j + (n + 1)) + 52
        have hn : nt ≤ n * K + 2 := by
          simpa only [loopBound, K, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnt
        have hb' : nb + 2 ≤ K := by
          dsimp [stepBound] at hnb
          dsimp [K]
          omega
        change nb + nt + 2 ≤ (n + 1) * K + 2
        nlinarith

theorem loop_eval (D : ℕ) (t zero one : Coefficient p μ)
    (minusOne : Word (baseWidth p μ)) (width : List Bool) (base : Store) (i j n : ℕ)
    (H : Environment p μ M D t zero one minusOne width base i)
    (a : Partial p μ D) (regs : Fin 16 → Bool) :
    ∃ ticks ≤ loopBound D (baseWidth p μ) i j n, ∃ rf,
      Eval SubexpLagrangeCacheControl.innerLoop ticks
        (⟨regs, view p μ M D base zero one j a (List.replicate n true)⟩ : Data)
        ⟨rf, view p μ M D base zero one (j + n)
          (run p μ M D t zero one minusOne i j n a) []⟩ := by
  obtain ⟨costs, ticks, rf, hv, ht⟩ := visits p μ M D t zero one minusOne width base i H n j a regs
  exact ⟨ticks, ht, rf, hv.eval⟩

end SubexponentialSAT.SubexpLagrangeCacheInner

end OAI.Algorithms
