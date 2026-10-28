import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpAlgorithm
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentCode
import OAI.Algorithms.SubexponentialSAT.SubexpInputCode
import OAI.Algorithms.SubexponentialSAT.SubexpTableInterpolation
import OAI.Algorithms.SubexponentialSAT.SubexpWeightCode

namespace OAI.Algorithms

/-!
# Constructing the separated program from finite coefficient data

The input consists of finite factor tables, residue rows, Taylor coefficient
arrays, support lists, outer base points, and individual color increments.
Every factor argument and every weight is computed from these data. No field
of the input contains a correct answer or a ready-made group expression.

The only enumeration of assignments is an outer list followed by one separate
inner list for each color. The Cartesian product of inner lists is never
constructed. The bounds keep the number of colors, table rows, variables,
factors, and interpolation coefficients visible.
-/

namespace SubexponentialSAT.SubexpProgramBuilder

open scoped BigOperators

abbrev Expr := Algorithm.Expr
abbrev Raw (D : ℕ) (A : Type*) := SymbolicCost.CoeffList D A

/-- Stored data for one factor at one interpolation node. `origin` is over the
residue field; `taylor` stores the coefficients of each shifted row path. -/
structure FactorData (D p q r : ℕ) (K A : Type*) where
  arity : ℕ
  color : Fin r
  origin : Fin arity → Fin D → K
  taylor : Fin arity → Fin (q + 1) → Fin D → A
  table : List (SubexpTableInterpolation.Row p arity A)

variable {D p q r : ℕ} {K A : Type*}

/-- Compute the lifted original linear form, then emit the marked Taylor
argument as a finite raw coefficient list. -/
def argument [Zero K] [Add K] [Mul K] [Neg A] (lift : K → A)
    (f : FactorData D p q r K A) (x : Fin D → K) (i : Fin f.arity) : Raw D A :=
  SubexpArgumentCode.compileArgument
    (SubexpInputCode.beta lift (f.origin i) x) (f.taylor i)

@[simp] theorem argument_length [Zero K] [Add K] [Mul K] [Neg A] (lift : K → A)
    (f : FactorData D p q r K A) (x : Fin D → K) (i : Fin f.arity) :
    (argument lift f x i).length = 2 + (q + 1) * D := by
  exact SubexpArgumentCode.length_compileArgument _ _

/-- Tensor interpolation is evaluated in factored Horner form. Each input
literal is the explicit argument above, not a polynomial-valued oracle. -/
def factorExpr [Zero K] [Add K] [Mul K] [One A] [Neg A]
    (lift : K → A) (cache : List (List A))
    (f : FactorData D p q r K A) (x : Fin D → K) : Expr (Raw D A) :=
  letI : Zero (Raw D A) := ⟨[]⟩
  letI : One (Raw D A) := ⟨SubexpAlgorithm.rawOne D⟩
  SubexpTableInterpolation.tableExpr (SubexpWeightCode.rawScalar D) cache f.table
    (fun i => .lit (argument lift f x i))

/-- Only the factors assigned to this color are multiplied. -/
def groupExpr [Zero K] [Add K] [Mul K] [One A] [Neg A]
    (lift : K → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A)) (g : Fin r) (x : Fin D → K) :
    Expr (Raw D A) :=
  letI : One (Raw D A) := ⟨SubexpAlgorithm.rawOne D⟩
  Algorithm.Expr.product
    ((factors.filter (fun f => decide (f.color = g))).map fun f => factorExpr lift cache f x)

def factorBudget (k M L : ℕ) : ℕ := 1 + M * (4 + k * (2 + 4 * L))

def groupBudget (m k M L : ℕ) : ℕ := m * (factorBudget k M L + 1) + 1

theorem factorExpr_size_le [Zero K] [Add K] [Mul K] [One A] [Neg A]
    (lift : K → A) (cache : List (List A))
    (f : FactorData D p q r K A) (x : Fin D → K) (k M L : ℕ)
    (hc : ∀ i : Fin p, (cache.getD i.val []).length ≤ L)
    (hk : f.arity ≤ k) (hM : f.table.length ≤ M) :
    (factorExpr lift cache f x).size ≤ factorBudget k M L := by
  let _ : Zero (Raw D A) := ⟨[]⟩
  let _ : One (Raw D A) := ⟨SubexpAlgorithm.rawOne D⟩
  have hs := SubexpTableInterpolation.tableExpr_size_le
    (SubexpWeightCode.rawScalar D) cache f.table
    (fun i => Algorithm.Expr.lit (argument lift f x i)) L 1 hc (fun _ => by rfl)
  change (factorExpr lift cache f x).size ≤ _ at hs
  apply hs.trans
  dsimp [factorBudget]
  simp only [Nat.mul_comm L 4]
  gcongr

theorem groupExpr_size_le [Zero K] [Add K] [Mul K] [One A] [Neg A]
    (lift : K → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A)) (g : Fin r) (x : Fin D → K)
    (k M L : ℕ)
    (hc : ∀ i : Fin p, (cache.getD i.val []).length ≤ L)
    (hk : ∀ f ∈ factors, f.arity ≤ k)
    (hM : ∀ f ∈ factors, f.table.length ≤ M) :
    (groupExpr lift cache factors g x).size ≤ groupBudget factors.length k M L := by
  let _ : One (Raw D A) := ⟨SubexpAlgorithm.rawOne D⟩
  let fs := factors.filter (fun f => decide (f.color = g))
  have hf : ∀ f ∈ fs, (factorExpr lift cache f x).size ≤ factorBudget k M L := by
    intro f h
    have hm : f ∈ factors := (List.mem_filter.mp h).1
    exact factorExpr_size_le lift cache f x k M L hc (hk f hm) (hM f hm)
  have hs := SubexpTableInterpolation.sum_map_le_length_mul fs
    (fun f => (factorExpr lift cache f x).size) (factorBudget k M L) hf
  have hl : fs.length ≤ factors.length := List.length_filter_le _ _
  simp only [groupExpr, Algorithm.Expr.size_product, List.map_map,
    Function.comp_def, List.length_map]
  change (fs.map (fun f => (factorExpr lift cache f x).size)).sum + fs.length + 1 ≤ _
  unfold groupBudget
  nlinarith

/-- Addition happens in the residue field before applying the chosen lift. -/
def shifted [Add K] (base increment : Fin D → K) : Fin D → K :=
  fun i => base i + increment i

variable {F : Type*}

def block [Add F] [Zero K] [Add K] [Mul K] [One A] [Mul A] [Neg A]
    (embed : F → K) (betaLift : K → A) (weightLift : F → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (base : Fin D → F) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    SubexpAlgorithm.Block (Raw D A) :=
  SubexpAlgorithm.Block.ofFibers
    (SubexpWeightCode.rawWeightWithCost (fun i => weightLift (base i)) a outside).1
    increments
    (fun g y => (SubexpWeightCode.rawWeightWithCost
      (fun i => weightLift (shifted base y i)) a (supports g)).1)
    (fun g y => groupExpr betaLift cache factors g (fun i => embed (shifted base y i)))

def blocks [Add F] [Zero K] [Add K] [Mul K] [One A] [Mul A] [Neg A]
    (embed : F → K) (betaLift : K → A) (weightLift : F → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → F)) (increments : Fin r → List (Fin D → F))
    (a : Fin D → ℕ) : List (SubexpAlgorithm.Block (Raw D A)) :=
  bases.map fun base => block embed betaLift weightLift cache factors supports outside base increments a

/-- The complete coefficient-list jet algorithm generated from stored input
data. In particular, group expressions are built inside this definition. -/
def executeJet [Add F] [Semiring K] [CommRing A]
    (embed : F → K) (betaLift : K → A) (weightLift : F → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → F)) (increments : Fin r → List (Fin D → F)) : List A :=
  SubexpAlgorithm.executeJet
    (blocks embed betaLift weightLift cache factors supports outside bases increments)

@[simp] theorem block_colors [Add F] [Zero K] [Add K] [Mul K] [One A] [Mul A] [Neg A]
    (embed : F → K) (betaLift : K → A) (weightLift : F → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (base : Fin D → F) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    (block embed betaLift weightLift cache factors supports outside base increments a).groups.length = r := by
  simp [block]

@[simp] theorem block_innerCalls [Add F] [Zero K] [Add K] [Mul K] [One A] [Mul A] [Neg A]
    (embed : F → K) (betaLift : K → A) (weightLift : F → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (base : Fin D → F) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    (block embed betaLift weightLift cache factors supports outside base increments a).innerCalls =
      ∑ g, (increments g).length := by
  exact SubexpAlgorithm.Block.ofFibers_innerCalls _ _ _ _

theorem blocks_size_le [Add F] [Zero K] [Add K] [Mul K] [One A] [Mul A] [Neg A]
    (embed : F → K) (betaLift : K → A) (weightLift : F → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → F)) (increments : Fin r → List (Fin D → F))
    (a : Fin D → ℕ) (k M L : ℕ)
    (hc : ∀ i : Fin p, (cache.getD i.val []).length ≤ L)
    (hk : ∀ f ∈ factors, f.arity ≤ k)
    (hM : ∀ f ∈ factors, f.table.length ≤ M) :
    (SubexpAlgorithm.rawMomentExpression
      (blocks embed betaLift weightLift cache factors supports outside bases increments a)).size ≤
      ((groupBudget factors.length k M L + 3) * (∑ g, (increments g).length) +
        2 * r + 4) * bases.length + 1 := by
  let _ : Zero (Raw D A) := ⟨[]⟩
  let _ : One (Raw D A) := ⟨SubexpAlgorithm.rawOne D⟩
  let bs := blocks embed betaLift weightLift cache factors supports outside bases increments a
  have ht : ∀ b ∈ bs, ∀ ts ∈ b.groups, ∀ t ∈ ts,
      t.group.size ≤ groupBudget factors.length k M L := by
    intro b hb ts hts t ht
    obtain ⟨base, hbase, rfl⟩ := List.mem_map.mp hb
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hts
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ht
    exact groupExpr_size_le betaLift cache factors g
      (fun i => embed (shifted base y i)) k M L hc hk hM
  have hr : ∀ b ∈ bs, b.groups.length ≤ r := by
    intro b hb
    obtain ⟨base, hbase, rfl⟩ := List.mem_map.mp hb
    simp
  have h := SubexpAlgorithm.momentExpression_size_le bs
    (groupBudget factors.length k M L) r ht hr
  have hi : (bs.map SubexpAlgorithm.Block.innerCalls).sum =
      bases.length * (∑ g, (increments g).length) := by
    simp [bs, blocks, List.map_map, Function.comp_def, List.map_const',
      List.sum_replicate, smul_eq_mul]
  have hl : bs.length = bases.length := by simp [bs, blocks]
  rw [hi, hl] at h
  change (SubexpAlgorithm.momentExpression bs).size ≤ _
  apply h.trans_eq
  ring

section Semantics

variable [Semiring K] [CommRing A]

noncomputable def argumentValue (lift : K → A)
    (f : FactorData D p q r K A) (x : Fin D → K) (i : Fin f.arity) :
    SymbolicCost.Poly D A :=
  WeightedSupport.incidenceArgument
    (SubexpInputCode.beta lift (f.origin i) x)
    (SubexpArgumentCode.semanticRow (f.taylor i) 0)
    ((Finset.range (q + 1)).erase 0) (SubexpArgumentCode.semanticRow (f.taylor i))

theorem argument_correct (lift : K → A)
    (f : FactorData D p q r K A) (x : Fin D → K) (i : Fin f.arity) :
    SymbolicCost.denote (argument lift f x i) = argumentValue lift f x i :=
  SubexpArgumentCode.denote_compileArgument _ _

noncomputable def factorValue (lift : K → A)
    (v : Fin p → A) (hu : TableInterpolation.UnitDifferences v)
    (f : FactorData D p q r K A) (x : Fin D → K) : SymbolicCost.Poly D A :=
  MvPolynomial.eval₂ WeightedSupport.scalarHom (argumentValue lift f x)
    (SubexpTableInterpolation.tablePolynomial v hu f.table)

theorem factorExpr_correct (lift : K → A) (cache : List (List A))
    (v : Fin p → A) (hu : TableInterpolation.UnitDifferences v)
    (hc : ∀ i : Fin p, PolynomialAlgorithm.denote (cache.getD i.val []) =
      TableInterpolation.basis v hu i)
    (f : FactorData D p q r K A) (x : Fin D → K) :
    ((factorExpr lift cache f x).map SymbolicCost.denote).eval =
      factorValue lift v hu f x := by
  let _ : Zero (Raw D A) := ⟨[]⟩
  let _ : One (Raw D A) := ⟨SubexpAlgorithm.rawOne D⟩
  unfold factorExpr
  rw [SubexpTableInterpolation.tableExpr_correct
    (R := A) (A := Raw D A) (S := SymbolicCost.Poly D A)
    (SubexpWeightCode.rawScalar D) SymbolicCost.denote WeightedSupport.scalarHom
    (by rfl) (SubexpAlgorithm.rawOne_denote D)
    (SubexpWeightCode.rawScalar_denote D) v hu cache hc]
  simp only [Algorithm.Expr.map, Algorithm.Expr.eval, argument_correct, factorValue]

theorem groupExpr_correct (lift : K → A) (cache : List (List A))
    (v : Fin p → A) (hu : TableInterpolation.UnitDifferences v)
    (hc : ∀ i : Fin p, PolynomialAlgorithm.denote (cache.getD i.val []) =
      TableInterpolation.basis v hu i)
    (factors : List (FactorData D p q r K A)) (g : Fin r) (x : Fin D → K) :
    ((groupExpr lift cache factors g x).map SymbolicCost.denote).eval =
      ((factors.filter (fun f => decide (f.color = g))).map
        (fun f => factorValue lift v hu f x)).prod := by
  let _ : One (Raw D A) := ⟨SubexpAlgorithm.rawOne D⟩
  unfold groupExpr
  rw [SubexpTableInterpolation.eval_map_product
    (A := Raw D A) (S := SymbolicCost.Poly D A) SymbolicCost.denote
    (SubexpAlgorithm.rawOne_denote D)]
  simp only [List.map_map, Function.comp_def, factorExpr_correct lift cache v hu hc]

end Semantics

end SubexponentialSAT.SubexpProgramBuilder

end OAI.Algorithms
