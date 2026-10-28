import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceWeights

namespace OAI.Algorithms

/-! A measured framed-list traversal for the actual moment source program.
The relational result permits each called weight program to return its
physical coefficient word without assuming a canonical byte encoding. -/

namespace SubexponentialSAT.SubexpMomentSourceProgram

open BitProgram StructuredCalls

def afterTag {α : Type*} (ctx : Context) (r : Fin 8 → Bool)
    (encode : α → Word) (xs : List α) (rest captured : Word)
    (buffers : SubexpBlockAssembly.Buffers) : Data :=
  match xs with
  | [] => state ctx (flags r false true (r 2)) rest buffers [] [] [] captured
  | x :: xs => state ctx (flags r true true (r 2))
      (Encoding.frame (encode x) ++ (Encoding.encodeList encode xs ++ rest)) buffers [] [] [] captured

theorem popList_eval {α : Type*} (ctx : Context) (r : Fin 8 → Bool)
    (encode : α → Word) (xs : List α) (rest captured : Word)
    (buffers : SubexpBlockAssembly.Buffers) :
    Eval (base SubexpBlockAssembly.popTag) 2
      (state ctx r (Encoding.encodeList encode xs ++ rest) buffers [] [] [] captured)
      (afterTag ctx r encode xs rest captured buffers) := by
  cases xs with
  | nil =>
      simpa only [Encoding.encodeList,List.singleton_append,afterTag] using
        base_eval ctx r (false :: rest) rest buffers buffers [] [] [] [] captured false true (r 2)
          (SubexpBlockAssembly.popTag_measured false (r 0) (r 1) (r 2) rest ctx.zero ctx.one buffers)
  | cons x xs =>
      simpa only [Encoding.encodeList,List.cons_append,List.append_assoc,afterTag] using
        base_eval ctx r
          (true :: (Encoding.frame (encode x) ++ (Encoding.encodeList encode xs ++ rest)))
          (Encoding.frame (encode x) ++ (Encoding.encodeList encode xs ++ rest))
          buffers buffers [] [] [] [] captured true true (r 2)
          (SubexpBlockAssembly.popTag_measured true (r 0) (r 1) (r 2)
            (Encoding.frame (encode x) ++ (Encoding.encodeList encode xs ++ rest)) ctx.zero ctx.one buffers)

def scanSteps {α β : Type*} (encode : α → Word) (cost : α → β → ℕ)
    (xs : List α) (ys : List β) : ℕ :=
  (List.zipWith (fun x y => 9*(encode x).length + cost x y + 11) xs ys).sum

/-- Every body invocation is a fixed command with an actual Eval derivation.
The source proof instantiates these premises with the descriptor/term/group
programs; this lemma supplies only their framed list control. -/
theorem scan_relational {α β : Type*} (ctx : Context) (body : Code)
    (encode : α → Word) (cost : α → β → ℕ) (relation : α → β → Prop)
    (update : β → SubexpBlockAssembly.Buffers → SubexpBlockAssembly.Buffers)
    (inv : SubexpBlockAssembly.Buffers → Prop)
    (hbody : ∀ x r rest captured buffers, inv buffers →
      ∃ y n rf, relation x y ∧ n ≤ cost x y ∧
        Eval body n (state ctx r (encode x ++ rest) buffers [] [] [] captured)
          (state ctx rf rest (update y buffers) [] [] [] captured))
    (hpreserve : ∀ x y buffers, relation x y → inv buffers → inv (update y buffers))
    (xs : List α) (r : Fin 8 → Bool) (rest captured : Word)
    (buffers : SubexpBlockAssembly.Buffers) (hinv : inv buffers) :
    ∃ ys n rf, List.Forall₂ relation xs ys ∧ n ≤ 3 + scanSteps encode cost xs ys ∧
      Eval (scan body) n
        (state ctx r (Encoding.encodeList encode xs ++ rest) buffers [] [] [] captured)
        (state ctx rf rest (ys.foldl (fun b y => update y b) buffers) [] [] [] captured) := by
  have loop : ∀ (xs : List α) r buffers, inv buffers →
      ∃ ys n rf, List.Forall₂ relation xs ys ∧ n ≤ 1 + scanSteps encode cost xs ys ∧
        Eval (.while 0 (.seq (base SubexpBlockAssembly.unframe)
          (.seq body (base SubexpBlockAssembly.popTag)))) n
          (afterTag ctx r encode xs rest captured buffers)
          (state ctx rf rest (ys.foldl (fun b y => update y b) buffers) [] [] [] captured) := by
    intro xs
    induction xs with
    | nil =>
        intro r buffers hinv
        exact ⟨[],1,flags r false true (r 2),.nil,by simp [scanSteps],Eval.while_false rfl⟩
    | cons x xs ih =>
        intro r buffers hinv
        let tail := Encoding.encodeList encode xs ++ rest
        let rp := flags r true true (r 2)
        let rb := flags rp false false (rp 2)
        have hu := base_eval ctx rp (Encoding.frame (encode x) ++ tail) (encode x ++ tail)
          buffers buffers [] [] [] [] captured false false (rp 2)
          (SubexpBlockAssembly.unframe_measured (rp 0) (rp 1) (rp 2)
            (encode x) tail ctx.zero ctx.one buffers)
        obtain ⟨y,nb,rf,hxy,hnb,hb⟩ := hbody x rb tail captured buffers hinv
        have hp := popList_eval ctx rf encode xs rest captured (update y buffers)
        obtain ⟨ys,nt,rt,hys,hnt,ht⟩ := ih rf (update y buffers)
          (hpreserve x y buffers hxy hinv)
        have h := Eval.while_true
          (by rfl : (afterTag ctx r encode (x::xs) rest captured buffers).regs 0 = true)
          (Eval.seq hu (Eval.seq hb hp)) ht
        refine ⟨y::ys,_,rt,.cons hxy hys,?_,h⟩
        simp only [scanSteps,List.zipWith_cons_cons,List.sum_cons] at *
        omega
  obtain ⟨ys,n,rf,hys,hn,h⟩ := loop xs r buffers hinv
  refine ⟨ys,2+n,rf,hys,by omega,?_⟩
  exact Eval.seq (popList_eval ctx r encode xs rest captured buffers) h

end SubexponentialSAT.SubexpMomentSourceProgram

end OAI.Algorithms
