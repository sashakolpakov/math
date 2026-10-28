import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorJet
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentSemanticsSelected

namespace OAI.Algorithms

/-! One executed factor step, specialized to the actual source ring, its
computed multiplication table, and the three physical assignment masters. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor.Semantics
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native
open LeafProgram.NativeSemantics LeafProgram.AssignmentSemantics
open scoped BigOperators

variable {r Q d n : ℕ}

theorem context_table_correct (p : SourceBank.Parameters r Q d) (u J : ℕ)
    (width : List Bool) (hw : width.length=baseWidth 3 p.t) (i j : Fin d) :
    RingBasis.basis (p.model.F p.t) i * RingBasis.basis (p.model.F p.t) j =
      ∑ k, LiftRing.of (p.model.F p.t)
        (wordValue 3 p.t ((sourceContext p n u J width hw).table i j k)) *
        RingBasis.basis (p.model.F p.t) k :=
  model_table_correct p.t p.ht p.hd p.model p.modulus p.cache i j

theorem basis_zero (p : SourceBank.Parameters r Q d) :
    RingBasis.basis (p.model.F p.t) (⟨0,p.hd⟩ : Fin d) = 1 := by
  simp [RingBasis.basis]

/-- Multiplication clips at the existing shared-U and jet cutoffs. The seed
need not be supplied with an artificial untruncated representative. -/
theorem product_step (p : SourceBank.Parameters r Q d) (u J : ℕ)
    (width : List Bool) (hw : width.length=baseWidth 3 p.t)
    (seed factor : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (hseed : Good Finset.univ u J seed) (hfactor : Good Finset.univ u J factor)
    (value : Squarefree.Jet (Fin n) (p.model.O p.t))
    (hv : rawDenote p.ops.decode factor = Squarefree.canonical u J value) :
    let next := MomentsProgram.Product.run 3 p.t p.modulus p.cache
      (sourceContext p n u J width hw).table u J seed factor []
    Good Finset.univ u J next ∧ rawDenote p.ops.decode next =
      Squarefree.canonical u J (rawDenote p.ops.decode seed * value) := by
  dsimp only
  refine ⟨product_good 3 p.t p.modulus p.cache _ Finset.univ u J seed factor hseed hfactor,?_⟩
  have hp := product_denote 3 p.t p.modulus p.cache (LiftRing.of (p.model.F p.t))
    (RingBasis.basis (p.model.F p.t)) (sourceContext p n u J width hw).table
    (context_table_correct p u J width hw) u J seed factor
  change rawDenote p.ops.decode _ = Squarefree.canonical u J
    (rawDenote p.ops.decode seed * rawDenote p.ops.decode factor) at hp
  rw [hv,Moments.canonical_mul_right] at hp
  exact hp

noncomputable def hashValue (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J f : ℕ) (width : List Bool) (hw : width.length=baseWidth 3 p.t)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool)
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (code : RingProgram.Code (RingProgram.ScalarCode 3 p.t) (3*p.t)) :
    Squarefree.Jet (Fin n) (p.model.O p.t) :=
  letI : CommRing (Squarefree.Poly (Fin n) (p.model.O p.t)) := inferInstance
  letI : CommRing (Squarefree.ZJet (Fin n) (p.model.O p.t)) := inferInstance
  letI : CommRing (Squarefree.Jet (Fin n) (p.model.O p.t)) := inferInstance
  indicatorPolynomial (sourceContext p n u J width hw) (LiftRing.of (p.model.F p.t)) code
    (MvPolynomial.eval (fun v : Fin n => factorJet p ps P n f v.val theta s)
      (rowPolynomial (scalarJet (V:=Fin n)) (sourceTerms p.ops.decode
        (HashInputProgram.Expansion.weightedRow p.t d source terms))))

noncomputable def markedValue (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (f : ℕ) (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (s : Fin 768 → List Bool) (ls : List (SAT.Literal (Fin n))) :
    Squarefree.Jet (Fin n) (p.model.O p.t) :=
  letI : CommRing (Squarefree.Poly (Fin n) (p.model.O p.t)) := inferInstance
  letI : CommRing (Squarefree.ZJet (Fin n) (p.model.O p.t)) := inferInstance
  letI : CommRing (Squarefree.Jet (Fin n) (p.model.O p.t)) := inferInstance
  MvPolynomial.eval (fun v : Fin n => factorJet p ps P n f v.val theta s)
    (clausePolynomial (R:=Squarefree.Jet (Fin n) (p.model.O p.t)) ls)

/-- Exact expanded raw hash followed by its indicator and seed multiplication. -/
theorem hash_step (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J f : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (width : List Bool) (hw : width.length=baseWidth 3 p.t)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (hone : Good Finset.univ u J one) (hseed : Good Finset.univ u J seed)
    (hi : ∀ v, Good Finset.univ u J (incidence v))
    (hminus : p.ops.decode minus = -1)
    (honeval : rawDenote p.ops.decode one = Squarefree.canonical u J 1)
    (hinc : ∀ v, rawDenote p.ops.decode (incidence v) = Squarefree.canonical u J
      (factorJet p ps P n f v.val theta s))
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (code : RingProgram.Code (RingProgram.ScalarCode 3 p.t) (3*p.t)) :
    let ctx := sourceContext p n u J width hw
    let factor := Indicator.result ctx minus one incidence
      (HashInputProgram.Expansion.weightedRow p.t d source terms)
      (List.ofFn (IdempotentApplyProgram.coefficientTriple p.t code))
    let next := MomentsProgram.Product.run 3 p.t p.modulus p.cache ctx.table u J seed factor []
    Good Finset.univ u J next ∧ rawDenote p.ops.decode next =
      Squarefree.canonical u J (rawDenote p.ops.decode seed *
        hashValue p ps P u J f width hw theta s source terms code) := by
  dsimp only
  apply product_step p u J width hw seed _ hseed
  · exact indicator_good (sourceContext p n u J width hw) Finset.univ hu hJ
      minus one incidence hone hi _ _
  · have hden := indicator_denote (sourceContext p n u J width hw) (LiftRing.of (p.model.F p.t))
      (RingBasis.basis (p.model.F p.t)) (context_table_correct p u J width hw)
      p.hd (basis_zero p) hu hJ Finset.univ minus one incidence hone hi hminus honeval
      (fun v => factorJet p ps P n f v.val theta s)
      (HashInputProgram.Expansion.weightedRow p.t d source terms)
      (fun _ _ l _ => hinc l.variable) code
    change rawDenote p.ops.decode _ =
      Squarefree.canonical u J (hashValue p ps P u J f width hw theta s source terms code) at hden
    exact hden

/-- The marked row uses its clause fold directly; it has no hash idempotent. -/
theorem marked_step (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J f : ℕ) (width : List Bool) (hw : width.length=baseWidth 3 p.t)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (hone : Good Finset.univ u J one) (hseed : Good Finset.univ u J seed)
    (hi : ∀ v, Good Finset.univ u J (incidence v))
    (hminus : p.ops.decode minus = -1)
    (honeval : rawDenote p.ops.decode one = Squarefree.canonical u J 1)
    (hinc : ∀ v, rawDenote p.ops.decode (incidence v) = Squarefree.canonical u J
      (factorJet p ps P n f v.val theta s))
    (ls : List (SAT.Literal (Fin n))) :
    let ctx := sourceContext p n u J width hw
    let factor := DynamicFold.value (Clause.step 3 p.t p.modulus p.cache ctx.table
      minus one incidence u J) ls one
    let next := MomentsProgram.Product.run 3 p.t p.modulus p.cache ctx.table u J seed factor []
    Good Finset.univ u J next ∧ rawDenote p.ops.decode next =
      Squarefree.canonical u J (rawDenote p.ops.decode seed * markedValue p ps P f theta s ls) := by
  dsimp only
  apply product_step p u J width hw seed _ hseed
  · exact clause_fold_good 3 p.t p.modulus p.cache _ Finset.univ u J
      minus one incidence hone hi ls one hone
  · have hden := clause_list_polynomial_scoped 3 p.t p.modulus p.cache (LiftRing.of (p.model.F p.t))
      (RingBasis.basis (p.model.F p.t)) (sourceContext p n u J width hw).table
      (context_table_correct p u J width hw) Finset.univ u J minus one incidence hone
      hminus honeval (fun v => factorJet p ps P n f v.val theta s) ls (fun l _ => hinc l.variable)
    change rawDenote p.ops.decode _ =
      Squarefree.canonical u J (markedValue p ps P f theta s ls) at hden
    exact hden

end SubexponentialSAT.SqrtLog.LeafProgram.Factor.Semantics

end OAI.Algorithms
