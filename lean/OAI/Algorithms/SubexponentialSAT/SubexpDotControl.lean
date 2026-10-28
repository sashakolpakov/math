import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpInputFrames
import OAI.Algorithms.SubexponentialSAT.SubexpInputCode

namespace OAI.Algorithms

/-!
# Fixed-control dot products on serialized field elements

The multiplication and addition interfaces below are actual finite-program
trace contracts. The concrete endpoint instantiates them with flat quartic
arithmetic at modulus p. Stack 77 is the accumulator and stack 78 is the stream
of row/input pairs; both remain outside the 77-stack multiplication service.
-/

namespace SubexponentialSAT.SubexpDotControl

open BitProgram StructuredCalls SubexpScanPrimitives
open scoped BigOperators

abbrev Data := State 8 79

def mulStore (modulus reduction width left right product : List Bool) (j : Fin 77) : List Bool :=
  if j = 66 then modulus else if j = 70 then left else if j = 71 then right
  else if j = 72 then product else if j = 73 then reduction else if j = 74 then width else []

def dotStore (modulus reduction width acc source left right product : List Bool)
    (j : Fin 79) : List Bool :=
  if j = 66 then modulus else if j = 70 then left else if j = 71 then right
  else if j = 72 then product else if j = 73 then reduction else if j = 74 then width
  else if j = 77 then acc else if j = 78 then source else []

def dataState (regs : Fin 8 → Bool)
    (modulus reduction width acc source left right product : List Bool) : Data :=
  ⟨regs, dotStore modulus reduction width acc source left right product⟩

def addStore (modulus width left right : List Bool) (j : Fin 20) : List Bool :=
  if j = 5 then modulus else if j = 8 then left else if j = 9 then right
  else if j = 10 then width else []

def mulPorts : Fin 77 → Fin 79 := Fin.castAdd 2

theorem mulPorts_injective : Function.Injective mulPorts := Fin.castAdd_injective _ _

def addPorts (j : Fin 20) : Fin 79 :=
  if j = 5 then 66 else if j = 8 then 77 else if j = 9 then 72
  else if j = 10 then 74 else ⟨j.val, by omega⟩

theorem addPorts_injective : Function.Injective addPorts := by decide

private theorem mulPorts_large (j : Fin 79) (h : ¬ ∃ i, mulPorts i = j) :
    j = 77 ∨ j = 78 := by
  have hj : 77 ≤ j.val := by
    by_contra hn
    exact h ⟨⟨j.val, by omega⟩, Fin.ext rfl⟩
  have hv : j.val = 77 ∨ j.val = 78 := by omega
  exact hv.imp Fin.ext Fin.ext

theorem embed_mul (regs frameRegs : Fin 8 → Bool)
    (modulus reduction width acc source left right product oldLeft oldRight oldProduct : List Bool) :
    embedState id mulPorts
      (dataState frameRegs modulus reduction width acc source oldLeft oldRight oldProduct)
      ⟨regs, mulStore modulus reduction width left right product⟩ =
      dataState regs modulus reduction width acc source left right product := by
  apply embedState_eq id mulPorts Function.injective_id mulPorts_injective
  · intro i; rfl
  · intro i
    fin_cases i <;> rfl
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    rcases mulPorts_large j hj with rfl | rfl <;> rfl

theorem embed_add (regs frameRegs : Fin 8 → Bool)
    (modulus reduction width source acc product oldAcc oldProduct : List Bool) :
    embedState id addPorts
      (dataState frameRegs modulus reduction width oldAcc source [] [] oldProduct)
      ⟨regs, addStore modulus width acc product⟩ =
      dataState regs modulus reduction width acc source [] [] product := by
  apply embedState_eq id addPorts Function.injective_id addPorts_injective
  · intro i; rfl
  · intro i
    fin_cases i <;> rfl
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    have ha : j ≠ 77 := by intro h; exact hj ⟨8, h.symm⟩
    have hp : j ≠ 72 := by intro h; exact hj ⟨9, h.symm⟩
    simp [dataState, dotStore, ha, hp]

abbrev MulContract {C : Type*} {L : ℕ} (program : Program 8 77 L)
    (B : ℕ) (encode : C → List Bool) (mul : C → C → C)
    (modulus reduction width : List Bool) : Prop :=
  ∀ (regs : Fin 8 → Bool) (a b : C), ∃ finalRegs,
    RunsIn program (400000 * (B + 1)^2)
      ⟨some program.entry, regs, mulStore modulus reduction width (encode a) (encode b) []⟩
      ⟨none, finalRegs, mulStore modulus reduction width [] [] (encode (mul a b))⟩

abbrev AddContract {C : Type*} {L : ℕ} (program : Program 8 20 L)
    (B : ℕ) (encode : C → List Bool) (add : C → C → C)
    (modulus width : List Bool) : Prop :=
  ∀ (regs : Fin 8 → Bool) (a b : C), ∃ finalRegs,
    RunsIn program (25000 * (B + 1)^2)
      ⟨some program.entry, regs, addStore modulus width (encode a) (encode b)⟩
      ⟨none, finalRegs, addStore modulus width (encode (add a b)) []⟩

abbrev multiply {L : ℕ} (program : Program 8 77 L) : Cmd 8 79 :=
  .call (ProgramLinking.liftProgram program id mulPorts)

abbrev addProduct {L : ℕ} (program : Program 8 20 L) : Cmd 8 79 :=
  .call (ProgramLinking.liftProgram program id addPorts)

theorem multiply_execute {C : Type*} {L : ℕ} (program : Program 8 77 L)
    (B : ℕ) (encode : C → List Bool) (mul : C → C → C)
    (modulus reduction width : List Bool)
    (hc : MulContract program B encode mul modulus reduction width)
    (regs : Fin 8 → Bool) (acc source : List Bool) (a b : C) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ 400000 * (B + 1)^2 ∧
      Eval (multiply program) n
        (dataState regs modulus reduction width acc source (encode a) (encode b) [])
        (dataState rf modulus reduction width acc source [] [] (encode (mul a b))) := by
  obtain ⟨rf, n, hn, ht⟩ := hc regs a b
  have h := eval_call_lifted program id mulPorts
    (dataState regs modulus reduction width acc source (encode a) (encode b) [])
    Function.injective_id mulPorts_injective
    (a := ⟨regs, mulStore modulus reduction width (encode a) (encode b) []⟩)
    (b := ⟨rf, mulStore modulus reduction width [] [] (encode (mul a b))⟩) ht
  rw [embed_mul, embed_mul] at h
  exact ⟨n, rf, hn, h⟩

theorem addProduct_execute {C : Type*} {L : ℕ} (program : Program 8 20 L)
    (B : ℕ) (encode : C → List Bool) (add : C → C → C)
    (modulus reduction width : List Bool)
    (hc : AddContract program B encode add modulus width)
    (regs : Fin 8 → Bool) (source : List Bool) (acc product : C) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ 25000 * (B + 1)^2 ∧
      Eval (addProduct program) n
        (dataState regs modulus reduction width (encode acc) source [] [] (encode product))
        (dataState rf modulus reduction width (encode (add acc product)) source [] [] []) := by
  obtain ⟨rf, n, hn, ht⟩ := hc regs acc product
  have h := eval_call_lifted program id addPorts
    (dataState regs modulus reduction width (encode acc) source [] [] (encode product))
    Function.injective_id addPorts_injective
    (a := ⟨regs, addStore modulus width (encode acc) (encode product)⟩)
    (b := ⟨rf, addStore modulus width (encode (add acc product)) []⟩) ht
  rw [embed_add, embed_add] at h
  exact ⟨n, rf, hn, h⟩

def payload {C : Type*} (encode : C → List Bool) (pair : C × C) : List Bool :=
  Encoding.frame (encode pair.1).reverse ++ Encoding.frame (encode pair.2).reverse

abbrev encodePairs {C : Type*} (encode : C → List Bool) : List (C × C) → List Bool
  | [] => [false]
  | pair :: rest => true :: (payload encode pair ++ encodePairs encode rest)

abbrev pairCommand {LM LA : ℕ} (pm : Program 8 77 LM) (pa : Program 8 20 LA) : Cmd 8 79 :=
  .seq (SubexpInputFrames.readField 78 70 (by decide))
    (.seq (SubexpInputFrames.readField 78 71 (by decide))
      (.seq (multiply pm) (addProduct pa)))

abbrev loop {LM LA : ℕ} (pm : Program 8 77 LM) (pa : Program 8 20 LA) : Cmd 8 79 :=
  .while 7 (.seq (pairCommand pm pa) (SubexpInputFrames.readTag 78))

abbrev command {LM LA : ℕ} (pm : Program 8 77 LM) (pa : Program 8 20 LA) : Cmd 8 79 :=
  .seq (SubexpInputFrames.readTag 78) (loop pm pa)

abbrev program {LM LA : ℕ} (pm : Program 8 77 LM) (pa : Program 8 20 LA) :
    Program 8 79 (size (command pm pa) + 1) := compiled (command pm pa) 78 77

theorem program_labels {LM LA : ℕ} (pm : Program 8 77 LM) (pa : Program 8 20 LA) :
    size (command pm pa) + 1 = LM + LA + 18 := by
  simp [ size, StructuredProgram.size]
  omega

theorem update_source (m t w acc source left right product tail : List Bool) :
    Function.update (dotStore m t w acc source left right product) 78 tail =
      dotStore m t w acc tail left right product := by
  funext j
  by_cases hj : j = 78
  · subst j; simp [dotStore]
  · simp [ dotStore, hj]

theorem update_left (m t w acc source left right product next : List Bool) :
    Function.update (dotStore m t w acc source left right product) 70 next =
      dotStore m t w acc source next right product := by
  funext j
  by_cases hj : j = 70
  · subst j; simp [dotStore]
  · simp [ dotStore, hj]

theorem update_right (m t w acc source left right product next : List Bool) :
    Function.update (dotStore m t w acc source left right product) 71 next =
      dotStore m t w acc source left next product := by
  funext j
  by_cases hj : j = 71
  · subst j; simp [dotStore]
  · simp [ dotStore, hj]

def pairCost (B : ℕ) : ℕ := 425000 * (B + 1)^2 + 48 * B + 8

theorem pair_execute {C : Type*} {LM LA : ℕ}
    (pm : Program 8 77 LM) (pa : Program 8 20 LA)
    (B : ℕ) (encode : C → List Bool) (mul add : C → C → C)
    (m t w : List Bool) (hm : MulContract pm B encode mul m t w)
    (ha : AddContract pa B encode add m w) (hlen : ∀ a, (encode a).length = 4 * B)
    (d : Data) (acc : C) (pair : C × C) (tail : List Bool)
    (hd : d.stacks = dotStore m t w (encode acc) (payload encode pair ++ tail) [] [] []) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ pairCost B ∧
      Eval (pairCommand pm pa) n d
        (dataState rf m t w (encode (add acc (mul pair.1 pair.2))) tail [] [] []) := by
  let rest := Encoding.frame (encode pair.2).reverse ++ tail
  obtain ⟨e1, he1, hs1⟩ := SubexpInputFrames.readField_execute 78 70 (by decide)
    d (encode pair.1).reverse rest (by
      rw [hd]
      simp [dotStore, payload, rest, List.append_assoc]) (by rw [hd]; rfl)
  have hh1 : e1.stacks = dotStore m t w (encode acc) rest (encode pair.1) [] [] := by
    rw [hs1, hd, update_source, update_left, List.reverse_reverse]
  obtain ⟨e2, he2, hs2⟩ := SubexpInputFrames.readField_execute 78 71 (by decide)
    e1 (encode pair.2).reverse tail (by rw [hh1]; rfl) (by rw [hh1]; rfl)
  have hh2 : e2.stacks = dotStore m t w (encode acc) tail (encode pair.1) (encode pair.2) [] := by
    rw [hs2, hh1, update_source, update_right, List.reverse_reverse]
  have e2eq : e2 = dataState e2.regs m t w (encode acc) tail (encode pair.1) (encode pair.2) [] :=
    state_ext rfl hh2
  obtain ⟨nm, rm, hnm, hem⟩ := multiply_execute pm B encode mul m t w hm
    e2.regs (encode acc) tail pair.1 pair.2
  obtain ⟨na, ra, hna, hea⟩ := addProduct_execute pa B encode add m t w ha rm tail acc (mul pair.1 pair.2)
  have hem' : Eval (multiply pm) nm e2
      (dataState rm m t w (encode acc) tail [] [] (encode (mul pair.1 pair.2))) := by
    rw [e2eq]
    exact hem
  refine ⟨_, ra, ?_, Eval.seq he1 (Eval.seq he2 (Eval.seq hem' hea))⟩
  simp only [List.length_reverse, hlen]
  unfold pairCost
  nlinarith

def foldPairs {C : Type*} (mul add : C → C → C) : C → List (C × C) → C
  | acc, [] => acc
  | acc, pair :: rest => foldPairs mul add (add acc (mul pair.1 pair.2)) rest

def listFlag {C : Type*} : List (C × C) → Bool
  | [] => false
  | _ :: _ => true

def afterTag {C : Type*} (encode : C → List Bool) : List (C × C) → List Bool → List Bool
  | [], suffix => suffix
  | pair :: rest, suffix => payload encode pair ++ encodePairs encode rest ++ suffix

theorem encodePairs_tag {C : Type*} (encode : C → List Bool)
    (pairs : List (C × C)) (suffix : List Bool) :
    encodePairs encode pairs ++ suffix = listFlag pairs :: afterTag encode pairs suffix := by
  cases pairs <;> simp [encodePairs, listFlag, afterTag, List.append_assoc]

theorem loop_execute {C : Type*} {LM LA : ℕ}
    (pm : Program 8 77 LM) (pa : Program 8 20 LA)
    (B : ℕ) (encode : C → List Bool) (mul add : C → C → C)
    (m t w : List Bool) (hm : MulContract pm B encode mul m t w)
    (ha : AddContract pa B encode add m w) (hlen : ∀ a, (encode a).length = 4 * B)
    (pairs : List (C × C)) (d : Data) (acc : C) (suffix : List Bool)
    (hd : d.stacks = dotStore m t w (encode acc) (afterTag encode pairs suffix) [] [] [])
    (hf : d.regs 7 = listFlag pairs) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ pairs.length * (pairCost B + 2) + 1 ∧
      Eval (loop pm pa) n d
        (dataState rf m t w (encode (foldPairs mul add acc pairs)) suffix [] [] []) := by
  induction pairs generalizing d acc with
  | nil =>
      refine ⟨1, d.regs, by simp, ?_⟩
      have heq : dataState d.regs m t w (encode (foldPairs mul add acc [])) suffix [] [] [] = d :=
        state_ext rfl hd.symm
      rw [heq]
      exact .while_false hf
  | cons pair rest ih =>
      obtain ⟨np, rp, hnp, hep⟩ := pair_execute pm pa B encode mul add m t w hm ha hlen
        d acc pair (encodePairs encode rest ++ suffix)
        (by simpa [afterTag, List.append_assoc] using hd)
      let middle := add acc (mul pair.1 pair.2)
      let ep := dataState rp m t w (encode middle) (encodePairs encode rest ++ suffix) [] [] []
      obtain ⟨et, het, hst, hft⟩ := SubexpInputFrames.readTag_execute 78 ep
        (listFlag rest) (afterTag encode rest suffix) (encodePairs_tag encode rest suffix)
      have hdt : et.stacks = dotStore m t w (encode middle) (afterTag encode rest suffix) [] [] [] := by
        rw [hst]
        exact update_source m t w (encode middle) _ [] [] [] _
      obtain ⟨nt, rt, hnt, hetail⟩ := ih et middle hdt hft
      refine ⟨np + 1 + nt + 1, rt, ?_, .while_true hf (.seq hep het) hetail⟩
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem program_execute {C : Type*} {LM LA : ℕ}
    (pm : Program 8 77 LM) (pa : Program 8 20 LA)
    (B : ℕ) (encode : C → List Bool) (mul add : C → C → C)
    (m t w : List Bool) (hm : MulContract pm B encode mul m t w)
    (ha : AddContract pa B encode add m w) (hlen : ∀ a, (encode a).length = 4 * B)
    (pairs : List (C × C)) (d : Data) (acc : C) (suffix : List Bool)
    (hd : d.stacks = dotStore m t w (encode acc) (encodePairs encode pairs ++ suffix) [] [] []) :
    ∃ rf : Fin 8 → Bool, RunsIn (program pm pa) (pairs.length * (pairCost B + 2) + 3)
      (d.withPC (some (program pm pa).entry))
      ((dataState rf m t w (encode (foldPairs mul add acc pairs)) suffix [] [] []).withPC none) := by
  obtain ⟨et, ht, hst, hft⟩ := SubexpInputFrames.readTag_execute 78 d
    (listFlag pairs) (afterTag encode pairs suffix) (by
      rw [hd]
      exact encodePairs_tag encode pairs suffix)
  have hdt : et.stacks = dotStore m t w (encode acc) (afterTag encode pairs suffix) [] [] [] := by
    rw [hst, hd, update_source]
  obtain ⟨n, rf, hn, he⟩ := loop_execute pm pa B encode mul add m t w hm ha hlen pairs et acc suffix hdt hft
  exact ⟨rf, 1 + n + 1, by omega, compiled_halt_trace (.seq ht he) 78 77⟩

theorem foldPairs_decode {C K : Type*} [Semiring K]
    (decode : C → K) (mul add : C → C → C)
    (hm : ∀ a b, decode (mul a b) = decode a * decode b)
    (ha : ∀ a b, decode (add a b) = decode a + decode b)
    (acc : C) (pairs : List (C × C)) :
    decode (foldPairs mul add acc pairs) =
      decode acc + (pairs.map (fun pair => decode pair.1 * decode pair.2)).sum := by
  induction pairs generalizing acc with
  | nil => simp [foldPairs]
  | cons pair rest ih => simp [foldPairs, ih, ha, hm, add_assoc]

def pairsFor {D : ℕ} {C : Type*} (row x : Fin D → C) : List (C × C) :=
  (List.finRange D).map (fun i => (row i, x i))

@[simp] theorem pairsFor_length {D : ℕ} {C : Type*} (row x : Fin D → C) :
    (pairsFor row x).length = D := by simp [pairsFor]

theorem foldPairs_dot {D : ℕ} {C K : Type*} [Semiring K]
    (decode : C → K) (mul add : C → C → C)
    (hm : ∀ a b, decode (mul a b) = decode a * decode b)
    (ha : ∀ a b, decode (add a b) = decode a + decode b)
    (zero : C) (hz : decode zero = 0) (row x : Fin D → C) :
    decode (foldPairs mul add zero (pairsFor row x)) =
      (SubexpInputCode.dotWithCost (fun i => decode (row i)) (fun i => decode (x i))).1 := by
  rw [foldPairs_decode decode mul add hm ha, hz, zero_add,
    SubexpInputCode.dotWithCost, SubexpInputCode.dotListWithCost_value]
  simp [pairsFor, List.map_map, Function.comp_def]

end SubexponentialSAT.SubexpDotControl

end OAI.Algorithms
