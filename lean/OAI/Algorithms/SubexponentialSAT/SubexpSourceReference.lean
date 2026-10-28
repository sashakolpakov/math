import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSourceFactors
import OAI.Algorithms.SubexponentialSAT.SubexpCountExecution

namespace OAI.Algorithms

/-!
# Factorwise refinement to the reference separated builder

The reference objects expose the individual factors already used by the
verified builder. This gives the physical source producer a local proof
interface: one weight and one factor at a time, with exact list incidence.
-/

namespace SubexponentialSAT.SubexpSourceReference

open SubexpBlockAssemblySemantics
open SubexpSourceSemantics
open SubexpProgramBuilder (FactorData)

section Relations

variable {D : ℕ} {C R : Type*} [One C] [CommRing R]

local instance : Zero (SymbolicCost.CoeffList D C) := ⟨[]⟩
local instance : One (SymbolicCost.CoeffList D C) := ⟨SubexpAlgorithm.rawOne D⟩
local instance : Zero (SymbolicCost.CoeffList D R) := ⟨[]⟩
local instance : One (SymbolicCost.CoeffList D R) := ⟨SubexpAlgorithm.rawOne D⟩

def FactorRel (decode : C → R)
    (actual : Factor C (SymbolicCost.CoeffList D C))
    (reference : Factor R (SymbolicCost.CoeffList D R)) : Prop :=
  ((actual.expression (SubexpWeightCode.rawScalar D)).map
    (fun raw => SymbolicCost.denote (decodeRaw decode raw))).eval =
  ((reference.expression (SubexpWeightCode.rawScalar D)).map SymbolicCost.denote).eval

def TermRel (decode : C → R)
    (actual : Term C (SymbolicCost.CoeffList D C))
    (reference : Term R (SymbolicCost.CoeffList D R)) : Prop :=
  SymbolicCost.denote (decodeRaw decode actual.weight) = SymbolicCost.denote reference.weight ∧
    List.Forall₂ (FactorRel decode) actual.factors reference.factors

def BlockRel (decode : C → R)
    (actual : Block C (SymbolicCost.CoeffList D C))
    (reference : Block R (SymbolicCost.CoeffList D R)) : Prop :=
  SymbolicCost.denote (decodeRaw decode actual.outside) = SymbolicCost.denote reference.outside ∧
    List.Forall₂ (List.Forall₂ (TermRel decode)) actual.groups reference.groups

private theorem forall₂_map {A B A' B' : Type*} {rel : A → B → Prop}
    {rel' : A' → B' → Prop} (f : A → A') (g : B → B')
    {xs : List A} {ys : List B} (h : List.Forall₂ rel xs ys)
    (he : ∀ a b, rel a b → rel' (f a) (g b)) :
    List.Forall₂ rel' (xs.map f) (ys.map g) := by
  induction h with
  | nil => exact .nil
  | @cons a b xs ys hab hrest ih => exact .cons (he a b hab) ih

theorem term_refines (decode : C → R) (hone : decode 1 = 1)
    {actual : Term C (SymbolicCost.CoeffList D C)}
    {reference : Term R (SymbolicCost.CoeffList D R)}
    (h : TermRel decode actual reference) :
    SubexpSourceSemantics.TermRel
      (fun raw => SymbolicCost.denote (decodeRaw decode raw)) SymbolicCost.denote
      (actual.expression (SubexpWeightCode.rawScalar D))
      (reference.expression (SubexpWeightCode.rawScalar D)) := by
  refine ⟨h.1,?_⟩
  apply product_value_eq
  · have he : decodeRaw decode (SubexpAlgorithm.rawOne D) =
        (SubexpAlgorithm.rawOne D : SymbolicCost.CoeffList D R) := by
      simp only [decodeRaw, SubexpAlgorithm.rawOne, List.map_cons, List.map_nil, hone]
    change SymbolicCost.denote (decodeRaw decode (SubexpAlgorithm.rawOne D)) = 1
    rw [he]
    exact SubexpAlgorithm.rawOne_denote D
  · exact SubexpAlgorithm.rawOne_denote D
  · exact forall₂_map _ _ h.2 (fun _ _ hab => hab)

theorem block_refines (decode : C → R) (hone : decode 1 = 1)
    {actual : Block C (SymbolicCost.CoeffList D C)}
    {reference : Block R (SymbolicCost.CoeffList D R)}
    (h : BlockRel decode actual reference) :
    SubexpSourceSemantics.BlockRel
      (fun raw => SymbolicCost.denote (decodeRaw decode raw)) SymbolicCost.denote
      (actual.expression (SubexpWeightCode.rawScalar D))
      (reference.expression (SubexpWeightCode.rawScalar D)) := by
  refine ⟨h.1,?_⟩
  exact forall₂_map _ _ h.2 (fun _ _ hg =>
    forall₂_map _ _ hg (fun _ _ ht => term_refines decode hone ht))

theorem jet_eq_reference (decode : C → R) (hone : decode 1 = 1)
    (actual : (Fin D → ℕ) → List (Block C (SymbolicCost.CoeffList D C)))
    (reference : (Fin D → ℕ) → List (Block R (SymbolicCost.CoeffList D R)))
    (h : ∀ a ∈ Algorithm.exponentList D (2*D+1),
      List.Forall₂ (BlockRel decode) (actual a) (reference a)) :
    Algorithm.executeRawJet (fun a =>
      (SubexpAlgorithm.momentExpression
        ((actual a).map (Block.expression (SubexpWeightCode.rawScalar D)))).map
          (decodeRaw decode)) =
      SubexpAlgorithm.executeJet (fun a =>
        (reference a).map (Block.expression (SubexpWeightCode.rawScalar D))) := by
  apply jet_eq_of_local decode
  · rfl
  · have he : decodeRaw decode (SubexpAlgorithm.rawOne D) =
        (SubexpAlgorithm.rawOne D : SymbolicCost.CoeffList D R) := by
      simp only [decodeRaw, SubexpAlgorithm.rawOne, List.map_cons, List.map_nil, hone]
    change SymbolicCost.denote (decodeRaw decode (SubexpAlgorithm.rawOne D)) = 1
    rw [he]
    exact SubexpAlgorithm.rawOne_denote D
  · intro a ha
    exact forall₂_map _ _ (h a ha) (fun _ _ hb => block_refines decode hone hb)

end Relations

section Builder

variable {D p q r : ℕ} {F K R : Type*}
  [Add F] [Zero K] [Add K] [Mul K] [One R] [Mul R] [Neg R]

def factor (lift : K → R) (cache : List (List R))
    (f : FactorData D p q r K R) (x : Fin D → K) :
    Factor R (SymbolicCost.CoeffList D R) :=
  ⟨p,f.arity,cache,SubexpProgramBuilder.argument lift f x,f.table⟩

def term (embed : F → K) (lift : K → R) (weightLift : F → R)
    (cache : List (List R)) (fs : List (FactorData D p q r K R))
    (support : List (Fin D)) (g : Fin r) (x : Fin D → F) (a : Fin D → ℕ) :
    Term R (SymbolicCost.CoeffList D R) :=
  ⟨(SubexpWeightCode.rawWeightWithCost (fun i => weightLift (x i)) a support).1,
    (fs.filter (fun f => decide (f.color = g))).map
      (fun f => factor lift cache f (fun i => embed (x i)))⟩

def block (embed : F → K) (lift : K → R) (weightLift : F → R)
    (cache : List (List R)) (fs : List (FactorData D p q r K R))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (base : Fin D → F) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    Block R (SymbolicCost.CoeffList D R) :=
  ⟨(SubexpWeightCode.rawWeightWithCost (fun i => weightLift (base i)) a outside).1,
    List.ofFn fun g => (increments g).map fun y =>
      term embed lift weightLift cache fs (supports g) g (SubexpProgramBuilder.shifted base y) a⟩

def blocks (embed : F → K) (lift : K → R) (weightLift : F → R)
    (cache : List (List R)) (fs : List (FactorData D p q r K R))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → F)) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    List (Block R (SymbolicCost.CoeffList D R)) :=
  bases.map fun base => block embed lift weightLift cache fs supports outside base increments a

theorem block_expression (embed : F → K) (lift : K → R) (weightLift : F → R)
    (cache : List (List R)) (fs : List (FactorData D p q r K R))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (base : Fin D → F) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    letI : Zero (SymbolicCost.CoeffList D R) := ⟨[]⟩
    letI : One (SymbolicCost.CoeffList D R) := ⟨SubexpAlgorithm.rawOne D⟩
    (block embed lift weightLift cache fs supports outside base increments a).expression
      (SubexpWeightCode.rawScalar D) =
      SubexpProgramBuilder.block embed lift weightLift cache fs supports outside base increments a := by
  let : Zero (SymbolicCost.CoeffList D R) := ⟨[]⟩
  let : One (SymbolicCost.CoeffList D R) := ⟨SubexpAlgorithm.rawOne D⟩
  simp only [block, term, factor, Block.expression, Term.expression, Factor.expression,
    SubexpProgramBuilder.block, SubexpAlgorithm.Block.ofFibers,
    SubexpProgramBuilder.groupExpr, SubexpProgramBuilder.factorExpr,
    List.map_ofFn, List.map_map, Function.comp_def]

theorem blocks_expression (embed : F → K) (lift : K → R) (weightLift : F → R)
    (cache : List (List R)) (fs : List (FactorData D p q r K R))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → F)) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    letI : Zero (SymbolicCost.CoeffList D R) := ⟨[]⟩
    letI : One (SymbolicCost.CoeffList D R) := ⟨SubexpAlgorithm.rawOne D⟩
    (blocks embed lift weightLift cache fs supports outside bases increments a).map
      (Block.expression (SubexpWeightCode.rawScalar D)) =
      SubexpProgramBuilder.blocks embed lift weightLift cache fs supports outside bases increments a := by
  let : Zero (SymbolicCost.CoeffList D R) := ⟨[]⟩
  let : One (SymbolicCost.CoeffList D R) := ⟨SubexpAlgorithm.rawOne D⟩
  simp only [blocks, SubexpProgramBuilder.blocks, List.map_map, Function.comp_def, block_expression]

end Builder

section Layout

open SubexpLayoutSpec

variable {D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F K R C : Type*} [Fintype F] [DecidableEq F] [One C]
  [Field K] [Fintype K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [CommRing R] {P : Factor.Pattern (Fin D) F}
  {c : Parameters p k Δ r tau} {L : Layout (E := K) P c}

local instance : Zero (SymbolicCost.CoeffList D C) := ⟨[]⟩
local instance : One (SymbolicCost.CoeffList D C) := ⟨SubexpAlgorithm.rawOne D⟩

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- Local packet semantics identify the generated source with the true
global-polynomial jet. No final jet, group program, or source-byte identity
is supplied as a premise. -/
theorem jet_eq_layoutJet
    (decode : C → R) (hone : decode 1 = 1)
    (actual : (Fin D → ℕ) → List (Block C (SymbolicCost.CoeffList D C)))
    (A : LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (sectionLift : CosetInvariance.ResidueSection A.residue)
    (t : Fin c.Q) (enum : EnumerationData L t)
    (cache : List (List R)) (labels : Fin p → R)
    (hu : TableInterpolation.UnitDifferences labels)
    (hcache : ∀ i : Fin p, PolynomialAlgorithm.denote (cache.getD i.val []) =
      TableInterpolation.basis labels hu i)
    (es : List F) (hnodup : es.Nodup) (hcomplete : ∀ e, e ∈ es)
    (data : F → FactorData D p c.R r K R)
    (ix : ∀ e, Fin (data e).arity ≃ {v // v ∈ P.scope e})
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (hcolor : ∀ e, (data e).color = L.color e t)
    (htable : ∀ e, SubexpTableInterpolation.tablePolynomial labels hu (data e).table =
      MvPolynomial.rename (ix e).symm (table e))
    (horigin : ∀ e i w, (data e).origin i w = (L.row e (ix e i) w).eval (L.node t))
    (htaylor : ∀ e i j w, (data e).taylor i j w =
      ((A.row e (ix e i) w).comp (Polynomial.X + Polynomial.C (A.theta t))).coeff j.val)
    (hnil : (p : R) ^ (D + 1) = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (hlocal : ∀ a ∈ Algorithm.exponentList D (2*D+1),
      List.Forall₂ (BlockRel decode) (actual a)
        (blocks (algebraMap (ZMod p) K) sectionLift.lift lift cache (es.map data)
          (SubexpEnumerationCode.supportLists L t) (SubexpEnumerationCode.outsideList L t)
          (SubexpEnumerationCode.outerBases enum) (SubexpEnumerationCode.innerIncrements enum) a)) :
    Algorithm.executeRawJet (fun a =>
      (SubexpAlgorithm.momentExpression
        ((actual a).map (Block.expression (SubexpWeightCode.rawScalar D)))).map
          (decodeRaw decode)) =
      (List.range D).map fun j =>
        (JetCRT.jet (A.theta t) D
          (GlobalPolynomial.rowGlobalPolynomial table A.row lift)).coeff j := by
  have href := jet_eq_reference decode hone actual
    (blocks (algebraMap (ZMod p) K) sectionLift.lift lift cache (es.map data)
      (SubexpEnumerationCode.supportLists L t) (SubexpEnumerationCode.outsideList L t)
      (SubexpEnumerationCode.outerBases enum) (SubexpEnumerationCode.innerIncrements enum)) hlocal
  simp only [blocks_expression] at href
  apply href.trans
  exact SubexpCountExecution.executeProgram_eq_jet A lift hLift sectionLift t enum
    cache labels hu hcache es hnodup hcomplete data ix table hcolor htable horigin htaylor hnil hker

end Layout

end SubexponentialSAT.SubexpSourceReference

end OAI.Algorithms
