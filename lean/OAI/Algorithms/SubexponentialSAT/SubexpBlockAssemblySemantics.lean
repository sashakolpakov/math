import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssembly

namespace OAI.Algorithms

/-! Exact source identity for concrete, possibly heterogeneous factor tables.
The only inputs are table rows, cache coefficients, coordinate literals, and
weights.  There is no assumed equality of whole groups or whole programs. -/

namespace SubexponentialSAT.SubexpBlockAssemblySemantics

open SubexpKernelControl (Word)

structure Factor (R A : Type*) where
  labels : ℕ
  arity : ℕ
  cache : List (List R)
  inputs : Fin arity → A
  rows : List (SubexpTableInterpolation.Row labels arity R)

def Factor.prepared {R A : Type*} (encode : A → Word) (literal : R → A)
    (f : Factor R A) : List SubexpTableSource.Row :=
  f.rows.map (SubexpTableSource.ofRow encode literal f.cache f.inputs)

def Factor.expression {R A : Type*} [Zero A] [One A]
    (literal : R → A) (f : Factor R A) : Algorithm.Expr A :=
  SubexpTableInterpolation.tableExpr literal f.cache f.rows (fun i => .lit (f.inputs i))

theorem Factor.source_eq {R A : Type*} [Zero A] [One A]
    (encode : A → Word) (literal : R → A) (f : Factor R A) :
    SubexpTableSource.tableCode (encode 0) (encode 1) (f.prepared encode literal) =
      SubexpPostfixControl.serializeCode encode (f.expression literal).compile :=
  SubexpTableSource.tableCode_eq encode literal f.cache f.inputs f.rows

structure Term (R A : Type*) where
  weight : A
  factors : List (Factor R A)

def Term.prepared {R A : Type*} (encode : A → Word) (literal : R → A)
    (t : Term R A) : SubexpBlockAssembly.Term :=
  ⟨encode t.weight,t.factors.map (Factor.prepared encode literal)⟩

def Term.expression {R A : Type*} [Zero A] [One A] (literal : R → A)
    (t : Term R A) : Algorithm.WeightedTerm A :=
  ⟨t.weight,Algorithm.Expr.product (t.factors.map (Factor.expression literal))⟩

theorem factors_source_eq {R A : Type*} [Zero A] [One A]
    (encode : A → Word) (literal : R → A) (fs : List (Factor R A)) :
    SubexpBlockAssembly.factorProduct (encode 0) (encode 1)
        (fs.map (Factor.prepared encode literal)) =
      SubexpPostfixControl.serializeCode encode
        (Algorithm.Expr.product (fs.map (Factor.expression literal))).compile := by
  simp [SubexpBlockAssembly.factorProduct,SubexpKernelControl.compile_product,
    List.map_map,Function.comp_def,Factor.source_eq]

theorem Term.compiled_eq {R A : Type*} [Zero A] [One A]
    (encode : A → Word) (literal : R → A) (t : Term R A) :
    SubexpBlockAssembly.compiledTerm (encode 0) (encode 1) (t.prepared encode literal) =
      SubexpKernelControl.ofTerm encode (t.expression literal) := by
  change SubexpKernelControl.Term.mk (encode t.weight)
      (SubexpBlockAssembly.factorProduct (encode 0) (encode 1)
        (t.factors.map (Factor.prepared encode literal))) =
    SubexpKernelControl.Term.mk (encode t.weight)
      (SubexpPostfixControl.serializeCode encode
        (Algorithm.Expr.product (t.factors.map (Factor.expression literal))).compile)
  rw [factors_source_eq]

structure Block (R A : Type*) where
  outside : A
  groups : List (List (Term R A))

def Block.prepared {R A : Type*} (encode : A → Word) (literal : R → A)
    (b : Block R A) : SubexpBlockAssembly.Block :=
  ⟨encode b.outside,b.groups.map (fun ts => ts.map (Term.prepared encode literal))⟩

def Block.expression {R A : Type*} [Zero A] [One A] (literal : R → A)
    (b : Block R A) : SubexpAlgorithm.Block A :=
  ⟨b.outside,b.groups.map (fun ts => ts.map (Term.expression literal))⟩

theorem Block.compiled_eq {R A : Type*} [Zero A] [One A]
    (encode : A → Word) (literal : R → A) (b : Block R A) :
    SubexpBlockAssembly.compiledBlock (encode 0) (encode 1) (b.prepared encode literal) =
      SubexpKernelControl.ofBlock encode (b.expression literal) := by
  simp [SubexpBlockAssembly.compiledBlock,Block.prepared,SubexpKernelControl.ofBlock,
    Block.expression,List.map_map,Function.comp_def,Term.compiled_eq]

/-- The output target of the concrete source constructor is exactly the
postfix compilation of the r-fold separated moment expression. -/
theorem source_eq {R A : Type*} [Zero A] [One A]
    (encode : A → Word) (literal : R → A) (bs : List (Block R A)) :
    SubexpKernelControl.momentCode (encode 0) (encode 1)
        ((bs.map (Block.prepared encode literal)).map
          (SubexpBlockAssembly.compiledBlock (encode 0) (encode 1))) =
      SubexpPostfixControl.serializeCode encode
        (SubexpAlgorithm.momentExpression (bs.map (Block.expression literal))).compile := by
  simpa only [List.map_map,Function.comp_def,Block.compiled_eq] using
    SubexpKernelControl.momentCode_eq encode (bs.map (Block.expression literal))

end SubexponentialSAT.SubexpBlockAssemblySemantics

end OAI.Algorithms
