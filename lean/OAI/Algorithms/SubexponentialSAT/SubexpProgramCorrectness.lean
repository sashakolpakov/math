import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpProgramBuilder
import OAI.Algorithms.SubexponentialSAT.SubexpComputedWeights
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationCode
import OAI.Algorithms.SubexponentialSAT.SubexpFactorCode

namespace OAI.Algorithms

/-!
# Concrete factor programs and the counting group polynomials

The premises describe the stored table, origin row, and Taylor coefficients
of each factor separately.  They do not assume equality of a group program,
moment, jet, or final count.  Local incidence indexing is handled by an
explicit equivalence, so the executable Fin arity can represent a scope type.
-/

namespace SubexponentialSAT.SubexpProgramCorrectness

noncomputable section

open scoped BigOperators

section LocalFactor

variable {D p q r : ℕ} {K A σ : Type*} [Semiring K] [CommRing A]

theorem argumentValue_eq_rowArgument
    (betaLift : K → A) (f : SubexpProgramBuilder.FactorData D p q r K A)
    (ix : Fin f.arity ≃ σ) (origin : σ → Fin D → K)
    (row : σ → Fin D → Polynomial A) (θ : A)
    (horigin : ∀ i w, f.origin i w = origin (ix i) w)
    (htaylor : ∀ i j w,
      f.taylor i j w = ((row (ix i) w).comp (Polynomial.X + Polynomial.C θ)).coeff j.val)
    (x : Fin D → K) (i : Fin f.arity) :
    SubexpProgramBuilder.argumentValue betaLift f x i =
      Counting.rowArgument (row (ix i)) θ
        (betaLift (∑ w, origin (ix i) w * x w)) q := by
  rw [← SubexpProgramBuilder.argument_correct]
  unfold SubexpProgramBuilder.argument
  rw [SubexpArgumentCode.denote_compileArgument_eq_rowArgument
    _ θ (f.taylor i) (row (ix i)) (htaylor i)]
  rw [SubexpInputCode.beta_eq_lift_sum]
  simp only [horigin]

theorem factorValue_eq_renamedTable
    (betaLift : K → A) (labels : Fin p → A)
    (hu : TableInterpolation.UnitDifferences labels)
    (f : SubexpProgramBuilder.FactorData D p q r K A)
    (ix : Fin f.arity ≃ σ) (table : MvPolynomial σ A)
    (htable : SubexpTableInterpolation.tablePolynomial labels hu f.table =
      MvPolynomial.rename ix.symm table)
    (x : Fin D → K) :
    SubexpProgramBuilder.factorValue betaLift labels hu f x =
      MvPolynomial.eval₂ WeightedSupport.scalarHom
        (SubexpProgramBuilder.argumentValue betaLift f x ∘ ix.symm) table := by
  unfold SubexpProgramBuilder.factorValue
  rw [htable, MvPolynomial.eval₂_rename]

end LocalFactor

section Group

variable {D p q r : ℕ} {K A E : Type*} {σ : E → Type*}
  [Semiring K] [CommRing A] [DecidableEq E]

/-- A list of concrete factor records produces the actual counting group.
The list may contain equal records for different factor identities; only
the original factor-index enumeration is required to have no duplicates. -/
theorem groupExpr_eq_rowGroup
    (betaLift : K → A) (cache : List (List A)) (labels : Fin p → A)
    (hu : TableInterpolation.UnitDifferences labels)
    (hcache : ∀ i : Fin p, PolynomialAlgorithm.denote (cache.getD i.val []) =
      TableInterpolation.basis labels hu i)
    (es : List E) (hnodup : es.Nodup)
    (data : E → SubexpProgramBuilder.FactorData D p q r K A)
    (ix : ∀ e, Fin (data e).arity ≃ σ e)
    (table : ∀ e, MvPolynomial (σ e) A)
    (origin : ∀ e, σ e → Fin D → K)
    (row : ∀ e, σ e → Fin D → Polynomial A) (θ : A)
    (htable : ∀ e, SubexpTableInterpolation.tablePolynomial labels hu (data e).table =
      MvPolynomial.rename (ix e).symm (table e))
    (horigin : ∀ e i w, (data e).origin i w = origin e (ix e i) w)
    (htaylor : ∀ e i j w,
      (data e).taylor i j w =
        ((row e (ix e i) w).comp (Polynomial.X + Polynomial.C θ)).coeff j.val)
    (g : Fin r) (x : Fin D → K) :
    ((SubexpProgramBuilder.groupExpr betaLift cache (es.map data) g x).map
      SymbolicCost.denote).eval =
      Counting.rowGroup (es.toFinset.filter (fun e => (data e).color = g))
        table row θ q (fun x e i => betaLift (∑ w, origin e i w * x w)) x := by
  rw [SubexpProgramBuilder.groupExpr_correct betaLift cache labels hu hcache]
  simp only [List.filter_map, List.map_map, Function.comp_def]
  have hf :
      (((es.filter fun e => decide ((data e).color = g)).map
        (fun e => SubexpProgramBuilder.factorValue betaLift labels hu (data e) x))).prod =
      (((es.filter fun e => decide ((data e).color = g)).map
        (fun e => MvPolynomial.eval₂ WeightedSupport.scalarHom
          (fun i => Counting.rowArgument (row e i) θ
            (betaLift (∑ w, origin e i w * x w)) q) (table e)))).prod := by
    congr 1
    apply List.map_congr_left
    intro e he
    refine (factorValue_eq_renamedTable betaLift labels hu (data e) (ix e) (table e)
      (htable e) x).trans ?_
    apply MvPolynomial.eval₂_congr
    intro i _ _ _
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      argumentValue_eq_rowArgument betaLift (data e) (ix e) (origin e) (row e) θ
        (horigin e) (htaylor e) x ((ix e).symm i)
  rw [hf]
  unfold Counting.rowGroup
  simpa only [List.toFinset_filter, decide_eq_true_eq] using
    (List.prod_toFinset
      (fun e => MvPolynomial.eval₂ WeightedSupport.scalarHom
        (fun i => Counting.rowArgument (row e i) θ
          (betaLift (∑ w, origin e i w * x w)) q) (table e))
      (hnodup.filter (fun e => decide ((data e).color = g)))).symm

end Group


section ActualLayout

open SubexpLayoutSpec

variable {D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F K R : Type*} [Fintype F] [DecidableEq F]
  [Field K] [Fintype K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [CommRing R] {P : Factor.Pattern (Fin D) F}
  {c : Parameters p k Δ r tau} {L : Layout (E := K) P c}

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- The semantic beta is exactly a section applied to the residue-row dot
product.  This is derived from residue compatibility of the lifted row. -/
theorem layoutBeta_eq_lift_sum (A : LiftedLayout L R) (coordinateLift : ZMod p → R)
    (hLift : ∀ z, A.residue (coordinateLift z) = algebraMap (ZMod p) K z)
    (sectionLift : CosetInvariance.ResidueSection A.residue) (t : Fin c.Q)
    (x : Fin D → ZMod p) (e : F) (i : {v // v ∈ P.scope e}) :
    SubexpCounting.layoutBeta A coordinateLift hLift sectionLift t x e i =
      sectionLift.lift (∑ w, (L.row e i w).eval (L.node t) *
        algebraMap (ZMod p) K (x w)) := by
  rw [SubexpCounting.layoutBeta, CosetInvariance.LiftedRow.beta_eq_lift_row]
  rfl

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
theorem compiledBeta_eq_layoutBeta (A : LiftedLayout L R) (coordinateLift : ZMod p → R)
    (hLift : ∀ z, A.residue (coordinateLift z) = algebraMap (ZMod p) K z)
    (sectionLift : CosetInvariance.ResidueSection A.residue) (t : Fin c.Q)
    (x : Fin D → ZMod p) (e : F) (i : {v // v ∈ P.scope e}) :
    SubexpInputCode.beta sectionLift.lift
        (fun w => (L.row e i w).eval (L.node t))
        (fun w => algebraMap (ZMod p) K (x w)) =
      SubexpCounting.layoutBeta A coordinateLift hLift sectionLift t x e i := by
  rw [SubexpInputCode.beta_eq_lift_sum, layoutBeta_eq_lift_sum]

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- Concrete factor data and local coefficient identities identify the
executed group expression with the actual layout counting group. -/
theorem groupExpr_eq_layoutGroup
    (A : LiftedLayout L R) (coordinateLift : ZMod p → R)
    (hLift : ∀ z, A.residue (coordinateLift z) = algebraMap (ZMod p) K z)
    (sectionLift : CosetInvariance.ResidueSection A.residue) (t : Fin c.Q)
    (cache : List (List R)) (labels : Fin p → R)
    (hu : TableInterpolation.UnitDifferences labels)
    (hcache : ∀ i : Fin p, PolynomialAlgorithm.denote (cache.getD i.val []) =
      TableInterpolation.basis labels hu i)
    (es : List F) (hnodup : es.Nodup) (hcomplete : ∀ e, e ∈ es)
    (data : F → SubexpProgramBuilder.FactorData D p c.R r K R)
    (ix : ∀ e, Fin (data e).arity ≃ {v // v ∈ P.scope e})
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (hcolor : ∀ e, (data e).color = L.color e t)
    (htable : ∀ e, SubexpTableInterpolation.tablePolynomial labels hu (data e).table =
      MvPolynomial.rename (ix e).symm (table e))
    (horigin : ∀ e i w, (data e).origin i w = (L.row e (ix e i) w).eval (L.node t))
    (htaylor : ∀ e i j w,
      (data e).taylor i j w =
        ((A.row e (ix e i) w).comp (Polynomial.X + Polynomial.C (A.theta t))).coeff j.val)
    (g : Fin r) (x : Fin D → ZMod p) :
    ((SubexpProgramBuilder.groupExpr sectionLift.lift cache (es.map data) g
      (fun w => algebraMap (ZMod p) K (x w))).map SymbolicCost.denote).eval =
      SubexpCounting.layoutGroup A coordinateLift hLift sectionLift table t g x := by
  have hes : es.toFinset = Finset.univ := by
    ext e
    simp [hcomplete e]
  have hset : es.toFinset.filter (fun e => (data e).color = g) =
      SubexpGlobalPolynomial.colorSet (fun e => L.color e t) g := by
    ext e
    simp [hes, hcolor, SubexpGlobalPolynomial.colorSet]
  have h := groupExpr_eq_rowGroup sectionLift.lift cache labels hu hcache es hnodup
    data ix table (fun e i w => (L.row e i w).eval (L.node t)) A.row (A.theta t)
    htable horigin htaylor g (fun w => algebraMap (ZMod p) K (x w))
  simpa only [hset, SubexpCounting.layoutGroup, Counting.rowGroup,
    layoutBeta_eq_lift_sum] using h

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- Own-coordinate invariance of the actual counting groups is derived
from the layout's beta invariance, with the supplied enumeration data. -/
theorem layoutGroup_enumeration_invariant
    (A : LiftedLayout L R) (coordinateLift : ZMod p → R)
    (hLift : ∀ z, A.residue (coordinateLift z) = algebraMap (ZMod p) K z)
    (sectionLift : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (t : Fin c.Q) (enum : EnumerationData L t)
    (o : Fin enum.outerCount) (g : Fin r)
    (x y : ∀ h, Fin (enum.innerCount h)) (hxy : x g = y g) :
    SubexpCounting.layoutGroup A coordinateLift hLift sectionLift table t g
        ((SubexpComputedWeights.enumerationFiberEquiv enum).symm ⟨o, x⟩) =
      SubexpCounting.layoutGroup A coordinateLift hLift sectionLift table t g
        ((SubexpComputedWeights.enumerationFiberEquiv enum).symm ⟨o, y⟩) := by
  apply Counting.rowGroup_congr
  intro e he i
  have hcolor : L.color e t = g :=
    (SubexpGlobalPolynomial.mem_colorSet (fun e => L.color e t) g e).mp he
  change (A.liftedRow coordinateLift hLift t e i).beta sectionLift
      (enum.assignmentEquiv.symm (o, x)) =
    (A.liftedRow coordinateLift hLift t e i).beta sectionLift
      (enum.assignmentEquiv.symm (o, y))
  rw [A.beta_enumeration_eq coordinateLift hLift sectionLift t enum e i o x,
    A.beta_enumeration_eq coordinateLift hLift sectionLift t enum e i o y]
  subst g
  rw [hxy]

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- The generated factor/group expressions satisfy the computed-weight
kernel theorem.  Both formerly local group premises (denotation and
own-coordinate invariance) are discharged here.  The remaining premises
identify only input tables, origin rows, and finite Taylor arrays. -/
theorem execute_groupPrograms_eq_separatedJet
    (A : LiftedLayout L R) (coordinateLift : ZMod p → R)
    (hLift : ∀ z, A.residue (coordinateLift z) = algebraMap (ZMod p) K z)
    (sectionLift : CosetInvariance.ResidueSection A.residue)
    (t : Fin c.Q) (enum : EnumerationData L t)
    (supports : Fin r → List (Fin D)) (hsnodup : ∀ g, (supports g).Nodup)
    (hsupport : ∀ g, (supports g).toFinset = L.support t g)
    (cache : List (List R)) (labels : Fin p → R)
    (hu : TableInterpolation.UnitDifferences labels)
    (hcache : ∀ i : Fin p, PolynomialAlgorithm.denote (cache.getD i.val []) =
      TableInterpolation.basis labels hu i)
    (es : List F) (hnodup : es.Nodup) (hcomplete : ∀ e, e ∈ es)
    (data : F → SubexpProgramBuilder.FactorData D p c.R r K R)
    (ix : ∀ e, Fin (data e).arity ≃ {v // v ∈ P.scope e})
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (hcolor : ∀ e, (data e).color = L.color e t)
    (htable : ∀ e, SubexpTableInterpolation.tablePolynomial labels hu (data e).table =
      MvPolynomial.rename (ix e).symm (table e))
    (horigin : ∀ e i w, (data e).origin i w = (L.row e (ix e i) w).eval (L.node t))
    (htaylor : ∀ e i j w,
      (data e).taylor i j w =
        ((A.row e (ix e i) w).comp (Polynomial.X + Polynomial.C (A.theta t))).coeff j.val) :
    SubexpAlgorithm.executeJet
      (SubexpComputedWeights.computedBlocks enum supports coordinateLift
        (fun _a o g y => SubexpProgramBuilder.groupExpr sectionLift.lift cache (es.map data) g
          (fun w => algebraMap (ZMod p) K
            (enum.outerBase o w + enum.increment g y w)))) =
      (List.range D).map fun j =>
        (SubexpCounting.separatedJet (D + 1) D
          (SubexpComputedWeights.enumerationFiberEquiv enum)
          (fun _ g => enum.zeroIndex g)
          (SubexpCounting.layoutGroup A coordinateLift hLift sectionLift table t)
          (fun a o => SubexpComputedWeights.outsideValue supports coordinateLift (enum.outerBase o) a)
          (fun a o g y => SubexpComputedWeights.insideValue supports coordinateLift
            (enum.outerBase o) (enum.increment g y) a g)).coeff j := by
  apply SubexpComputedWeights.execute_computedBlocks_eq_separatedJet enum supports
    hsnodup hsupport coordinateLift
    (fun _a o g y => SubexpProgramBuilder.groupExpr sectionLift.lift cache (es.map data) g
      (fun w => algebraMap (ZMod p) K (enum.outerBase o w + enum.increment g y w)))
    (SubexpCounting.layoutGroup A coordinateLift hLift sectionLift table t)
  · intro a o g y
    exact groupExpr_eq_layoutGroup A coordinateLift hLift sectionLift t cache labels hu hcache
      es hnodup hcomplete data ix table hcolor htable horigin htaylor g
      (enum.outerBase o + enum.increment g y)
  · exact layoutGroup_enumeration_invariant A coordinateLift hLift sectionLift table t enum

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- The same equality for the program built from the actual finite vector
lists.  Enumeration coverage, computed weights, group denotation, and group
invariance are all discharged by earlier theorems. -/
theorem executeProgram_eq_separatedJet
    (A : LiftedLayout L R) (coordinateLift : ZMod p → R)
    (hLift : ∀ z, A.residue (coordinateLift z) = algebraMap (ZMod p) K z)
    (sectionLift : CosetInvariance.ResidueSection A.residue)
    (t : Fin c.Q) (enum : EnumerationData L t)
    (cache : List (List R)) (labels : Fin p → R)
    (hu : TableInterpolation.UnitDifferences labels)
    (hcache : ∀ i : Fin p, PolynomialAlgorithm.denote (cache.getD i.val []) =
      TableInterpolation.basis labels hu i)
    (es : List F) (hnodup : es.Nodup) (hcomplete : ∀ e, e ∈ es)
    (data : F → SubexpProgramBuilder.FactorData D p c.R r K R)
    (ix : ∀ e, Fin (data e).arity ≃ {v // v ∈ P.scope e})
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (hcolor : ∀ e, (data e).color = L.color e t)
    (htable : ∀ e, SubexpTableInterpolation.tablePolynomial labels hu (data e).table =
      MvPolynomial.rename (ix e).symm (table e))
    (horigin : ∀ e i w, (data e).origin i w = (L.row e (ix e i) w).eval (L.node t))
    (htaylor : ∀ e i j w,
      (data e).taylor i j w =
        ((A.row e (ix e i) w).comp (Polynomial.X + Polynomial.C (A.theta t))).coeff j.val) :
    SubexpEnumerationCode.executeProgram enum (algebraMap (ZMod p) K) sectionLift.lift
      coordinateLift cache (es.map data) =
      (List.range D).map fun j =>
        (SubexpCounting.separatedJet (D + 1) D
          (SubexpComputedWeights.enumerationFiberEquiv enum)
          (fun _ g => enum.zeroIndex g)
          (SubexpCounting.layoutGroup A coordinateLift hLift sectionLift table t)
          (fun a o => SubexpComputedWeights.outsideValue
            (SubexpEnumerationCode.supportLists L t) coordinateLift (enum.outerBase o) a)
          (fun a o g y => SubexpComputedWeights.insideValue
            (SubexpEnumerationCode.supportLists L t) coordinateLift
              (enum.outerBase o) (enum.increment g y) a g)).coeff j := by
  apply SubexpEnumerationCode.executeProgram_eq_separatedJet enum (algebraMap (ZMod p) K)
    sectionLift.lift coordinateLift cache (es.map data)
    (SubexpCounting.layoutGroup A coordinateLift hLift sectionLift table t)
  · intro o g y
    exact groupExpr_eq_layoutGroup A coordinateLift hLift sectionLift t cache labels hu hcache
      es hnodup hcomplete data ix table hcolor htable horigin htaylor g
      (enum.outerBase o + enum.increment g y)
  · exact layoutGroup_enumeration_invariant A coordinateLift hLift sectionLift table t enum

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- Taylor arrays are computed from row syntax by `buildFactors`; callers
supply only the local meaning of those input expressions. -/
theorem executeBuiltFactors_eq_separatedJet
    (A : LiftedLayout L R) (coordinateLift : ZMod p → R)
    (hLift : ∀ z, A.residue (coordinateLift z) = algebraMap (ZMod p) K z)
    (sectionLift : CosetInvariance.ResidueSection A.residue)
    (t : Fin c.Q) (enum : EnumerationData L t)
    (cache : List (List R)) (labels : Fin p → R)
    (hu : TableInterpolation.UnitDifferences labels)
    (hcache : ∀ i : Fin p, PolynomialAlgorithm.denote (cache.getD i.val []) =
      TableInterpolation.basis labels hu i)
    (es : List F) (hnodup : es.Nodup) (hcomplete : ∀ e, e ∈ es)
    (source : F → SubexpFactorCode.FactorSource D p r K R)
    (ix : ∀ e, Fin (source e).arity ≃ {v // v ∈ P.scope e})
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (hcolor : ∀ e, (source e).color = L.color e t)
    (htable : ∀ e, SubexpTableInterpolation.tablePolynomial labels hu (source e).table =
      MvPolynomial.rename (ix e).symm (table e))
    (horigin : ∀ e i w, (source e).origin i w = (L.row e (ix e i) w).eval (L.node t))
    (hrow : ∀ e i w, ((source e).rows i w).denote = A.row e (ix e i) w) :
    SubexpEnumerationCode.executeProgram enum (algebraMap (ZMod p) K) sectionLift.lift
      coordinateLift cache
      (SubexpFactorCode.buildFactors (A.theta t) c.R (es.map source)).data =
      (List.range D).map fun j =>
        (SubexpCounting.separatedJet (D + 1) D
          (SubexpComputedWeights.enumerationFiberEquiv enum)
          (fun _ g => enum.zeroIndex g)
          (SubexpCounting.layoutGroup A coordinateLift hLift sectionLift table t)
          (fun a o => SubexpComputedWeights.outsideValue
            (SubexpEnumerationCode.supportLists L t) coordinateLift (enum.outerBase o) a)
          (fun a o g y => SubexpComputedWeights.insideValue
            (SubexpEnumerationCode.supportLists L t) coordinateLift
              (enum.outerBase o) (enum.increment g y) a g)).coeff j := by
  simpa only [SubexpFactorCode.buildFactors_data, List.map_map, Function.comp_def] using
    (executeProgram_eq_separatedJet A coordinateLift hLift sectionLift t enum
      cache labels hu hcache es hnodup hcomplete
      (fun e => (SubexpFactorCode.buildFactor (A.theta t) c.R (source e)).data)
      ix table hcolor htable horigin
      (fun e => SubexpFactorCode.buildFactor_taylor_of_denote
        (A.theta t) c.R (source e) (ix e) (A.row e) (hrow e)))

end ActualLayout

end

end SubexponentialSAT.SubexpProgramCorrectness

end OAI.Algorithms
