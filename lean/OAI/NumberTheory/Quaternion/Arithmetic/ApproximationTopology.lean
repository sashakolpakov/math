import OAI.NumberTheory.Quaternion.Arithmetic.LocalAdeles

/-! # Approximation Topology -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ApproximationTopology

noncomputable section

section

/-! The basic open sets in which Arithmetic must produce rational points.
These results construct and describe the target sets. They do not assert
that rational points meet them. -/

open scoped Classical RestrictedProduct
open Filter

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))

abbrev AwayPlace := {v : LocalAdeles.Place F // v ∉ S}

/-- Prescribed local open conditions at finitely many places, and integral
matrix conditions at every remaining place outside S. -/
def basicAdelicSet (T : Finset (AwayPlace S))
    (U : (v : AwayPlace S) → Set (LocalAdeles.LocalPoints G v.val)) : Set (LocalAdeles.AwayAdelicPoints G S) :=
  {a | (∀ v ∈ T, a v ∈ U v) ∧
    ∀ v, v ∉ T → a v ∈ LocalAdeles.integralLocalSubgroup G v.val}

theorem basicAdelicSet_isOpen (T : Finset (AwayPlace S))
    (U : (v : AwayPlace S) → Set (LocalAdeles.LocalPoints G v.val))
    (hU : ∀ v ∈ T, IsOpen (U v)) : IsOpen (basicAdelicSet G S T U) := by
  have hfinite : IsOpen {a : LocalAdeles.AwayAdelicPoints G S | ∀ v ∈ T, a v ∈ U v} := by
    simp only [Set.ofPred_forall]
    exact isOpen_biInter_finset fun v hv =>
      (hU v hv).preimage (LocalAdeles.awayAdelic_eval_continuous G S v)
  have hrest : IsOpen {a : LocalAdeles.AwayAdelicPoints G S |
      ∀ v, v ∉ T → a v ∈ LocalAdeles.integralLocalSubgroup G v.val} :=
    RestrictedProduct.isOpen_forall_imp_mem
      (fun v : AwayPlace S => LocalAdeles.integralLocalSubgroup_isOpen G v.val)
  exact hfinite.inter hrest

/-- Extend any prescribed finite tuple by the identity at the other places. -/
def finiteLocalTuple (T : Finset (AwayPlace S))
    (x : (v : AwayPlace S) → LocalAdeles.LocalPoints G v.val) : LocalAdeles.AwayAdelicPoints G S :=
  ⟨fun v => if v ∈ T then x v else 1, by
    filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
    change v ∉ T at hv
    change (if v ∈ T then x v else 1) ∈ LocalAdeles.integralLocalSubgroup G v.val
    rw [ite_eq_right hv]
    exact (LocalAdeles.integralLocalSubgroup G v.val).one_mem⟩

theorem basicAdelicSet_nonempty (T : Finset (AwayPlace S))
    (U : (v : AwayPlace S) → Set (LocalAdeles.LocalPoints G v.val))
    (hU : ∀ v ∈ T, (U v).Nonempty) : (basicAdelicSet G S T U).Nonempty := by
  let x : (v : AwayPlace S) → LocalAdeles.LocalPoints G v.val :=
    fun v => if hv : v ∈ T then (hU v hv).choose else 1
  refine ⟨finiteLocalTuple G S T x, ?_, ?_⟩
  · intro v hv
    change (if v ∈ T then x v else 1) ∈ U v
    simpa only [ite_eq_left hv, x, dite_eq_left hv] using (hU v hv).choose_spec
  · intro v hv
    change (if v ∈ T then x v else 1) ∈ LocalAdeles.integralLocalSubgroup G v.val
    simpa only [ite_eq_right hv] using (LocalAdeles.integralLocalSubgroup G v.val).one_mem

theorem diagonal_mem_basicAdelicSet_iff (T : Finset (AwayPlace S))
    (U : (v : AwayPlace S) → Set (LocalAdeles.LocalPoints G v.val)) (g : G.RationalPoints) :
    LocalAdeles.diagonalAway G S g ∈ basicAdelicSet G S T U ↔
      (∀ v ∈ T, LocalAdeles.diagonalLocal G v.val g ∈ U v) ∧
      ∀ v, v ∉ T → LocalAdeles.diagonalLocal G v.val g ∈ LocalAdeles.integralLocalSubgroup G v.val := Iff.rfl

/-- The finite local conditions form a basis for the actual restricted-product
topology. This is the topological reduction needed before the arithmetic proof. -/
theorem exists_basicAdelicSet_subset {V : Set (LocalAdeles.AwayAdelicPoints G S)}
    (hV : IsOpen V) (a : LocalAdeles.AwayAdelicPoints G S) (ha : a ∈ V) :
    ∃ (T : Finset (AwayPlace S))
      (U : (v : AwayPlace S) → Set (LocalAdeles.LocalPoints G v.val)),
      (∀ v ∈ T, IsOpen (U v)) ∧ a ∈ basicAdelicSet G S T U ∧
        basicAdelicSet G S T U ⊆ V := by
  let R := fun v : AwayPlace S => LocalAdeles.LocalPoints G v.val
  let I := fun v : AwayPlace S => (LocalAdeles.integralLocalSubgroup G v.val : Set (R v))
  have hsupport : {v : AwayPlace S | a v ∉ I v}.Finite :=
    Filter.eventually_cofinite.mp a.property
  let J := hsupport.toFinset
  have hJ : ∀ v : AwayPlace S, v ∉ J → a v ∈ I v := by
    intro v hv
    simpa only [J, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hv
  have hc : cofinite ≤ Filter.principal (J : Set (AwayPlace S))ᶜ :=
    Filter.le_principal_iff.mpr J.finite_toSet.compl_mem_cofinite
  let a₀ : Πʳ v, [R v, I v]_[Filter.principal (J : Set (AwayPlace S))ᶜ] :=
    ⟨a, fun v hv => hJ v hv⟩
  let inc := RestrictedProduct.inclusion R I hc
  have hopen : IsOpen (inc ⁻¹' V) :=
    hV.preimage (RestrictedProduct.continuous_inclusion hc)
  obtain ⟨W, hW, heq⟩ :=
    RestrictedProduct.isEmbedding_coe_of_principal.toIsInducing.isOpen_iff.mp hopen
  have haW : (fun v => a v) ∈ W := by
    change a₀ ∈ ((⇑) ⁻¹' W)
    rw [heq]
    exact ha
  obtain ⟨T, U, hU, hsub⟩ := isOpen_pi_iff.mp hW _ haW
  let U' : (v : AwayPlace S) → Set (LocalAdeles.LocalPoints G v.val) := fun v =>
    (if v ∈ T then U v else Set.univ) ∩ (if v ∈ J then Set.univ else I v)
  refine ⟨J ∪ T, U', ?_, ?_, ?_⟩
  · intro v _
    apply IsOpen.inter
    · by_cases hv : v ∈ T
      · simpa only [ite_eq_left hv] using (hU v hv).1
      · simp only [ite_eq_right hv, isOpen_univ]
    · by_cases hv : v ∈ J
      · simp only [ite_eq_left hv, isOpen_univ]
      · simpa only [ite_eq_right hv] using LocalAdeles.integralLocalSubgroup_isOpen G v.val
  · constructor
    · intro v _
      constructor
      · by_cases hv : v ∈ T
        · simpa only [ite_eq_left hv] using (hU v hv).2
        · simp only [ite_eq_right hv, Set.mem_univ]
      · by_cases hv : v ∈ J
        · simp only [ite_eq_left hv, Set.mem_univ]
        · simpa only [ite_eq_right hv] using hJ v hv
    · intro v hv
      exact hJ v (fun h => hv (Finset.mem_union_left T h))
  · intro b hb
    have hbI : ∀ v : AwayPlace S, v ∉ J → b v ∈ I v := by
      intro v hv
      by_cases hvT : v ∈ T
      · have h := (hb.1 v (Finset.mem_union_right J hvT)).2
        simpa only [ite_eq_right hv] using h
      · exact hb.2 v (by simp only [Finset.mem_union, not_or]; exact ⟨hv, hvT⟩)
    let b₀ : Πʳ v, [R v, I v]_[Filter.principal (J : Set (AwayPlace S))ᶜ] :=
      ⟨b, fun v hv => hbI v hv⟩
    have hbW : (fun v => b v) ∈ W := by
      apply hsub
      intro v hv
      change v ∈ T at hv
      have h := (hb.1 v (Finset.mem_union_right J hv)).1
      simpa only [ite_eq_left hv] using h
    have hb₀ : b₀ ∈ ((⇑) ⁻¹' W) := hbW
    rw [heq] at hb₀
    exact hb₀

/-- Reformulate density as the simultaneous finite local approximation problem.
This equivalence proves neither side on its own. -/
theorem denseRange_diagonalAway_iff :
    DenseRange (LocalAdeles.diagonalAway G S) ↔
      ∀ (T : Finset (AwayPlace S))
        (U : (v : AwayPlace S) → Set (LocalAdeles.LocalPoints G v.val)),
        (∀ v ∈ T, IsOpen (U v)) → (∀ v ∈ T, (U v).Nonempty) →
        ∃ g : G.RationalPoints, LocalAdeles.diagonalAway G S g ∈ basicAdelicSet G S T U := by
  constructor
  · intro hd T U ho hn
    exact hd.exists_mem_open (basicAdelicSet_isOpen G S T U ho)
      (basicAdelicSet_nonempty G S T U hn)
  · intro happ a
    rw [mem_closure_iff]
    intro V hV ha
    obtain ⟨T, U, ho, haU, hsub⟩ := exists_basicAdelicSet_subset G S hV a ha
    obtain ⟨g, hg⟩ := happ T U ho (fun v hv => ⟨a v, haU.1 v hv⟩)
    exact ⟨LocalAdeles.diagonalAway G S g, hsub hg, Set.mem_range_self g⟩

end

/-! A closed subgroup of the actual restricted product is the whole
group when it contains every single local factor. -/

open scoped Classical RestrictedProduct
open Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
  (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))

def awayMulSingleHom (v : AwayPlace S) : LocalAdeles.LocalPoints G v.val →* LocalAdeles.AwayAdelicPoints G S where
  toFun := RestrictedProduct.mulSingle (fun w : AwayPlace S => LocalAdeles.integralLocalSubgroup G w.val) v
  map_one' := RestrictedProduct.mulSingle_one _ _
  map_mul' x y := by
    apply RestrictedProduct.ext
    intro w
    exact congrFun (Pi.mulSingle_mul (f := fun w : AwayPlace S => LocalAdeles.LocalPoints G w.val) v x y) w

theorem finiteLocalTuple_insert (T : Finset (AwayPlace S)) (v : AwayPlace S) (hv : v ∉ T)
    (x : (w : AwayPlace S) → LocalAdeles.LocalPoints G w.val) :
    finiteLocalTuple G S (insert v T) x = awayMulSingleHom G S v (x v) * finiteLocalTuple G S T x := by
  apply RestrictedProduct.ext
  intro w
  change (if w ∈ insert v T then x w else 1) =
    Pi.mulSingle (M := fun w : AwayPlace S => LocalAdeles.LocalPoints G w.val) v (x v) w *
      (if w ∈ T then x w else 1)
  by_cases hw : w = v
  · subst w
    simp [hv]
  · simp [hw]

theorem finiteLocalTuple_mem_of_single (H : Subgroup (LocalAdeles.AwayAdelicPoints G S))
    (hH : ∀ (v : AwayPlace S) (g : LocalAdeles.LocalPoints G v.val), awayMulSingleHom G S v g ∈ H)
    (T : Finset (AwayPlace S)) (x : (v : AwayPlace S) → LocalAdeles.LocalPoints G v.val) :
    finiteLocalTuple G S T x ∈ H := by
  induction T using Finset.induction_on with
  | empty =>
    have he : finiteLocalTuple G S ∅ x = 1 := by
      apply RestrictedProduct.ext
      intro v
      simp [finiteLocalTuple]
    rw [he]
    exact H.one_mem
  | @insert v T hv ih =>
    rw [finiteLocalTuple_insert G S T v hv x]
    exact H.mul_mem (hH v (x v)) ih

theorem adelic_closed_subgroup_eq_top_of_single (H : Subgroup (LocalAdeles.AwayAdelicPoints G S))
    (hclosed : IsClosed (H : Set (LocalAdeles.AwayAdelicPoints G S)))
    (hH : ∀ (v : AwayPlace S) (g : LocalAdeles.LocalPoints G v.val), awayMulSingleHom G S v g ∈ H) : H = ⊤ := by
  apply top_unique
  intro a _
  apply hclosed.closure_subset
  rw [mem_closure_iff]
  intro V hV ha
  obtain ⟨T, U, _, haU, hsub⟩ := exists_basicAdelicSet_subset G S hV a ha
  refine ⟨finiteLocalTuple G S T a, hsub ⟨?_, ?_⟩,
    finiteLocalTuple_mem_of_single G S H hH T a⟩
  · intro v hv
    change (if v ∈ T then a v else 1) ∈ U v
    simpa only [ite_eq_left hv] using haU.1 v hv
  · intro v hv
    change (if v ∈ T then a v else 1) ∈ LocalAdeles.integralLocalSubgroup G v.val
    rw [ite_eq_right hv]
    exact (LocalAdeles.integralLocalSubgroup G v.val).one_mem

end

end OAI.NumberTheory.Quaternion.Arithmetic.ApproximationTopology
