import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateState
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Concrete prime-field points inside the template controller

The fixed PointBank program adds the stored base and increment modulo p.
Its scalar bank and constant-quartet stream are exact byte outputs; all
unrelated template buffers and arithmetic masters remain available.
-/

namespace SubexponentialSAT.SubexpTemplatePointServices

open BitProgram StructuredCalls SubexpScanPrimitives SubexpTemplateProgram
open SubexpLiftRing BinaryArithmetic

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev BaseWord (p : ℕ) := SubexpQuarticRing.Word (baseWidth p 1)

variable (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)

/-- The actual modular word addition used for each coordinate. -/
def scalarPoint {D : ℕ} (base increment : Fin D → BaseWord p) (i : Fin D) : BaseWord p :=
  (SubexpPreparedQuartic.wordAdd p 1 M (base i) (increment i)).1

/-- The residue-field coordinate supplied to the beta machine. -/
def quarticPoint {D : ℕ} (base increment : Fin D → BaseWord p) (i : Fin D) :
    SubexpInputBitProgram.ResidueCode p :=
  SubexpPointBank.constant p (scalarPoint p M base increment i)

def pointBank {D : ℕ} (base increment : Fin D → BaseWord p) : List Bool :=
  DensePolynomialLoop.flatten ((List.finRange D).map (scalarPoint p M base increment))

def pointStream {D : ℕ} (base increment : Fin D → BaseWord p) : List Bool :=
  Encoding.encodeList SubexpQuarticFlatMul.flat
    ((List.finRange D).map (quarticPoint p M base increment))

theorem pointWords_eq {D : ℕ} (base increment : Fin D → BaseWord p) :
    SubexpPointBank.pointWords p M ((List.finRange D).map base)
      ((List.finRange D).map increment) =
      (List.finRange D).map (scalarPoint p M base increment) :=
  SubexpPointBank.pointWords_map p M (List.finRange D) base increment

omit [Fact p.Prime] in
theorem quartetStream_eq {D : ℕ} (base increment : Fin D → BaseWord p) :
    SubexpPointBank.quartetStream p ((List.finRange D).map (scalarPoint p M base increment)) =
      pointStream p M base increment := by
  have he : @SubexpFlatAdd.encode (baseWidth p 1) = SubexpQuarticFlatMul.flat := by
    funext a
    exact (SubexpInputBitProgram.flat_eq_add_encode a).symm
  rw [SubexpPointBank.quartetStream_map, he]
  simp only [pointStream, List.map_map, Function.comp_def]
  rfl

omit [Fact p.Prime] in
theorem pointBank_length {D : ℕ} (base increment : Fin D → BaseWord p) :
    (pointBank p M base increment).length = D * baseWidth p 1 := by
  rw [pointBank, DensePolynomialLoop.flatten_length, List.length_map, List.length_finRange]

/-- Canonicality follows from the executed modular addition. -/
theorem scalarPoint_canonical {D : ℕ} (base increment : Fin D → BaseWord p) (i : Fin D) :
    BinaryArithmetic.toNat (scalarPoint p M base increment i).val < p := by
  simpa only [scalarPoint, pow_one] using
    SubexpPreparedQuartic.wordAdd_canonical p 1 M (base i) (increment i)

theorem scalarPoint_label {D : ℕ} (base increment : Fin D → BaseWord p) (i : Fin D) :
    BinaryArithmetic.toNat (scalarPoint p M base increment i).val =
      ((BinaryArithmetic.toNat (base i).val : ZMod p) + (BinaryArithmetic.toNat (increment i).val : ZMod p)).val :=
  SubexpPointBank.pointWord_canonical_label p M (base i) (increment i)

theorem quarticPoint_decode {D : ℕ} (source : SubexpSelectedConversions.Prepared p 0)
    (base increment : Fin D → BaseWord p) (i : Fin D) :
    source.residueRing.decode (quarticPoint p M base increment i) =
      algebraMap (ZMod p) (SubexpActualRing.E p)
        (SubexpWordLift.sourceValue p (base i) + SubexpWordLift.sourceValue p (increment i)) :=
  SubexpPointBank.point_constant_decode p M source (base i) (increment i)

omit [Fact p.Prime] in
theorem pointPorts_injective : Function.Injective pointPorts := by decide

def pointWork (w : Work) (bank point : List Bool) : Work :=
  { w with bank := bank, point := point }

theorem project_point (ctx : Context) (regs : Fin 8 → Bool) (w : Work) :
    projectState id pointPorts (state ctx regs w) =
      SubexpPointBank.ready regs ctx.sourceModulus ctx.sourceWidth w.base w.increment
        (List.replicate ctx.dimension true) w.bank w.point := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;> rfl

theorem embed_point (ctx : Context) (oldRegs regs : Fin 8 → Bool) (w : Work)
    (bank point : List Bool) :
    embedState id pointPorts (state ctx oldRegs w)
      (SubexpPointBank.ready regs ctx.sourceModulus ctx.sourceWidth w.base w.increment
        (List.replicate ctx.dimension true) bank point) =
      state ctx regs (pointWork w bank point) := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id pointPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    exact congrArg (fun d : State 8 32 => d.stacks i)
      (project_point ctx regs (pointWork w bank point))
  · intro i hi
    have h138 : i ≠ 138 := fun h => hi ⟨20, h.symm⟩
    have h91 : i ≠ 91 := fun h => hi ⟨21, h.symm⟩
    simp only [state_stack_eq, pointWork, h138, h91, ite_false]

/-- Exact execution of the PointBank call occurring in `termBody`.
The dimension counter is preserved; the two encoded vectors determine
the number of coordinates actually traversed. -/
theorem point_eval {D : ℕ} (base increment : Fin D → BaseWord p)
    (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (hm : ctx.sourceModulus = M.bits)
    (hw : ctx.sourceWidth.length = baseWidth p 1)
    (hb : w.base = DensePolynomialLoop.flatten ((List.finRange D).map base))
    (hi : w.increment = DensePolynomialLoop.flatten ((List.finRange D).map increment))
    (hbank : w.bank = []) (hpoint : w.point = []) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool),
      n ≤ SubexpPointBank.steps D (baseWidth p 1) ∧
      Eval (.call (ProgramLinking.liftProgram SubexpPointBank.program id pointPorts)) n
        (state ctx regs w)
        (state ctx rf (pointWork w (pointBank p M base increment) (pointStream p M base increment))) := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpPointBank.program_runs p M
    ((List.finRange D).map base) ((List.finRange D).map increment)
    (by simp) regs ctx.sourceWidth (List.replicate ctx.dimension true) hw
  simp only [pointWords_eq p M base increment, quartetStream_eq p M base increment] at ht
  change Trace _ n
    ((SubexpPointBank.ready regs M.bits ctx.sourceWidth
      (DensePolynomialLoop.flatten ((List.finRange D).map base))
      (DensePolynomialLoop.flatten ((List.finRange D).map increment))
      (List.replicate ctx.dimension true) [] []).withPC _)
    ((SubexpPointBank.ready rf M.bits ctx.sourceWidth
      (DensePolynomialLoop.flatten ((List.finRange D).map base))
      (DensePolynomialLoop.flatten ((List.finRange D).map increment))
      (List.replicate ctx.dimension true) (pointBank p M base increment)
      (pointStream p M base increment)).withPC _) at ht
  rw [← hm, ← hb, ← hi] at ht
  have he := eval_call_lifted SubexpPointBank.program id pointPorts (state ctx regs w)
    Function.injective_id pointPorts_injective ht
  rw [embed_point, embed_point] at he
  have hw0 : pointWork w [] [] = w := by
    cases w
    simp_all [pointWork]
  rw [hw0] at he
  exact ⟨n, rf, by simpa using hn, he⟩

/-- An explicit polynomial bound for the same actual call. -/
theorem point_eval_polynomial {D : ℕ} (base increment : Fin D → BaseWord p)
    (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (hm : ctx.sourceModulus = M.bits)
    (hw : ctx.sourceWidth.length = baseWidth p 1)
    (hb : w.base = DensePolynomialLoop.flatten ((List.finRange D).map base))
    (hi : w.increment = DensePolynomialLoop.flatten ((List.finRange D).map increment))
    (hbank : w.bank = []) (hpoint : w.point = []) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool),
      n ≤ 15000 * (D + 1) * (baseWidth p 1 + 1)^2 ∧
      Eval (.call (ProgramLinking.liftProgram SubexpPointBank.program id pointPorts)) n
        (state ctx regs w)
        (state ctx rf (pointWork w (pointBank p M base increment) (pointStream p M base increment))) := by
  obtain ⟨n, rf, hn, ht⟩ := point_eval p M base increment ctx regs w hm hw hb hi hbank hpoint
  exact ⟨n, rf, hn.trans (SubexpPointBank.steps_polynomial D (baseWidth p 1)), ht⟩

end SubexponentialSAT.SubexpTemplatePointServices

end OAI.Algorithms
