import OAI.NumberTheory.Quaternion.Arithmetic.FiniteIndex
import OAI.NumberTheory.Quaternion.Arithmetic.SelectedArithmeticProduct

/-! # Exceptional Approximation -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ExceptionalApproximation

noncomputable section

section

/-! The finite-index result fills the selected coordinates generated
by additive parameters, while leaving exceptional local factors explicit. -/

open scoped Classical
open Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

instance completionCharZero (v : LocalAdeles.Place F) : CharZero (LocalAdeles.Completion v) where
  cast_injective m n h := by
    have he : (m : F) = (n : F) := (LocalAdeles.localEmbedding v).injective (by
      simpa only [map_natCast] using h)
    exact Nat.cast_injective he

def localAdditiveGeneration (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : LocalAdeles.Place F) : Prop :=
  Subgroup.closure (Arithmetic.FiniteIndex.additiveParameterElements (K := LocalAdeles.Completion v) (G := LocalAdeles.LocalPoints G v)) = ⊤

theorem arithmetic_closure_contains_exceptional_identity
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) (B T : Finset (ApproximationTopology.AwayPlace S))
    (hindex : (Groups.arithmeticProjection G S T).range.topologicalClosure.FiniteIndex)
    (hgen : ∀ v : ApproximationTopology.AwayPlace S, v ∉ B → localAdditiveGeneration G v.val)
    (x : Groups.SelectedLocalProduct G S T) (hx : ∀ v : (T : Set (ApproximationTopology.AwayPlace S)), v.val ∈ B → x v = 1) :
    x ∈ (Groups.arithmeticProjection G S T).range.topologicalClosure := by
  let := hindex
  exact Arithmetic.FiniteIndex.finiteIndex_product_mem_of_exceptional_one (K := fun v : (T : Set (ApproximationTopology.AwayPlace S)) =>
    LocalAdeles.Completion v.val.val) (Groups.arithmeticProjection G S T).range.topologicalClosure
      {v | v.val ∈ B} (fun v hv => hgen v.val hv) x hx

end

section

/-! Approximate prescribed conditions at the exceptional places and
record the finite set of denominators of the resulting rational point. -/

open scoped Classical
open Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def localAdelicTarget (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) {S : Finset (LocalAdeles.Place F)}
    (T : Finset (ApproximationTopology.AwayPlace S)) (U : ∀ v : ApproximationTopology.AwayPlace S, Set (LocalAdeles.LocalPoints G v.val))
    (v : ApproximationTopology.AwayPlace S) : Set (LocalAdeles.LocalPoints G v.val) :=
  if v ∈ T then U v else LocalAdeles.integralLocalSubgroup G v.val

theorem localAdelicTarget_isOpen (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) {S : Finset (LocalAdeles.Place F)}
    (T : Finset (ApproximationTopology.AwayPlace S)) (U : ∀ v : ApproximationTopology.AwayPlace S, Set (LocalAdeles.LocalPoints G v.val))
    (hU : ∀ v ∈ T, IsOpen (U v)) (v : ApproximationTopology.AwayPlace S) : IsOpen (localAdelicTarget G T U v) := by
  by_cases hv : v ∈ T
  · simpa only [localAdelicTarget, ite_eq_left hv] using hU v hv
  · simpa only [localAdelicTarget, ite_eq_right hv] using LocalAdeles.integralLocalSubgroup_isOpen G v.val

theorem localAdelicTarget_nonempty (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) {S : Finset (LocalAdeles.Place F)}
    (T : Finset (ApproximationTopology.AwayPlace S)) (U : ∀ v : ApproximationTopology.AwayPlace S, Set (LocalAdeles.LocalPoints G v.val))
    (hU : ∀ v ∈ T, (U v).Nonempty) (v : ApproximationTopology.AwayPlace S) : (localAdelicTarget G T U v).Nonempty := by
  by_cases hv : v ∈ T
  · simpa only [localAdelicTarget, ite_eq_left hv] using hU v hv
  · exact ⟨1, by simpa only [localAdelicTarget, ite_eq_right hv] using!
      (LocalAdeles.integralLocalSubgroup G v.val).one_mem⟩

theorem exceptional_weakApproximation_point (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (B T : Finset (ApproximationTopology.AwayPlace S))
    (hweak : DenseRange (fun g : G.RationalPoints => fun v : (B : Set (ApproximationTopology.AwayPlace S)) =>
      LocalAdeles.diagonalLocal G v.val.val g))
    (U : ∀ v : ApproximationTopology.AwayPlace S, Set (LocalAdeles.LocalPoints G v.val))
    (hU : ∀ v ∈ T, IsOpen (U v)) (hne : ∀ v ∈ T, (U v).Nonempty) :
    ∃ a : G.RationalPoints, ∀ v ∈ B, LocalAdeles.diagonalLocal G v.val a ∈ localAdelicTarget G T U v := by
  let V := Set.pi univ (fun v : (B : Set (ApproximationTopology.AwayPlace S)) => localAdelicTarget G T U v.val)
  have hV : IsOpen V := isOpen_set_pi (Set.toFinite univ)
    (fun v _ => localAdelicTarget_isOpen G T U hU v.val)
  have hVne : V.Nonempty := by
    refine ⟨fun v => (localAdelicTarget_nonempty G T U hne v.val).choose, ?_⟩
    intro v _
    exact (localAdelicTarget_nonempty G T U hne v.val).choose_spec
  obtain ⟨a, ha⟩ := hweak.exists_mem_open hV hVne
  exact ⟨a, fun v hv => ha ⟨v, hv⟩ (mem_univ _)⟩

theorem rational_point_finite_denominators (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (a : G.RationalPoints) :
    ∃ D : Finset (ApproximationTopology.AwayPlace S), ∀ v : ApproximationTopology.AwayPlace S, v ∉ D →
      LocalAdeles.diagonalLocal G v.val a ∈ LocalAdeles.integralLocalSubgroup G v.val := by
  have hfin : {v : ApproximationTopology.AwayPlace S | LocalAdeles.diagonalLocal G v.val a ∉ LocalAdeles.integralLocalSubgroup G v.val}.Finite :=
    eventually_cofinite.mp (LocalAdeles.diagonalAway G S a).property
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  simpa only [Set.Finite.mem_toFinset, mem_ofPred_eq, not_not] using hv

end

section

/-! A rational approximation at exceptional factors can be corrected
at all other selected places while retaining integrality outside them. -/

open scoped Classical
open Set _root_.Topology

theorem arithmetic_correction_of_finiteIndex
    {F : Type} [Field F] [NumberField F] {n : ℕ}
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) (B T R : Finset (ApproximationTopology.AwayPlace S))
    (hTR : T ⊆ R)
    (hindex : (Groups.arithmeticProjection G S R).range.topologicalClosure.FiniteIndex)
    (hgen : ∀ v : ApproximationTopology.AwayPlace S, v ∉ B → localAdditiveGeneration G v.val)
    (U : ∀ v : ApproximationTopology.AwayPlace S, Set (LocalAdeles.LocalPoints G v.val))
    (hU : ∀ v ∈ T, IsOpen (U v)) (hne : ∀ v ∈ T, (U v).Nonempty)
    (a : G.RationalPoints)
    (haB : ∀ v ∈ B, LocalAdeles.diagonalLocal G v.val a ∈ localAdelicTarget G T U v)
    (haR : ∀ v : ApproximationTopology.AwayPlace S, v ∉ R → LocalAdeles.diagonalLocal G v.val a ∈ LocalAdeles.integralLocalSubgroup G v.val) :
    ∃ g : G.RationalPoints, ∀ v : ApproximationTopology.AwayPlace S,
      LocalAdeles.diagonalLocal G v.val g ∈ localAdelicTarget G T U v := by
  let z := fun v : ApproximationTopology.AwayPlace S => (localAdelicTarget_nonempty G T U hne v).choose
  have hz (v : ApproximationTopology.AwayPlace S) : z v ∈ localAdelicTarget G T U v :=
    (localAdelicTarget_nonempty G T U hne v).choose_spec
  let x : Groups.SelectedLocalProduct G S R := fun v =>
    if v.val ∈ B then 1 else (LocalAdeles.diagonalLocal G v.val.val a)⁻¹ * z v.val
  have hx (v : (R : Set (ApproximationTopology.AwayPlace S))) :
      LocalAdeles.diagonalLocal G v.val.val a * x v ∈ localAdelicTarget G T U v.val := by
    by_cases hv : v.val ∈ B
    · simpa only [x, ite_eq_left hv, mul_one] using haB v.val hv
    · simpa only [x, ite_eq_right hv, mul_inv_cancel_left] using hz v.val
  have hcl := arithmetic_closure_contains_exceptional_identity G S B R hindex hgen x
    (fun v hv => by simp only [x, ite_eq_left hv])
  let V := fun v : (R : Set (ApproximationTopology.AwayPlace S)) =>
    (fun y : LocalAdeles.LocalPoints G v.val.val => LocalAdeles.diagonalLocal G v.val.val a * y) ⁻¹'
      localAdelicTarget G T U v.val
  let W := Set.pi univ V
  have hW : IsOpen W := isOpen_set_pi (Set.toFinite univ) (fun v _ =>
    (localAdelicTarget_isOpen G T U hU v.val).preimage (continuous_const.mul continuous_id))
  have hxW : x ∈ W := fun v _ => hx v
  change x ∈ closure (range (Groups.arithmeticProjection G S R)) at hcl
  obtain ⟨y, hy, ⟨b, rfl⟩⟩ := mem_closure_iff.mp hcl W hW hxW
  refine ⟨a * b.val, fun v => ?_⟩
  by_cases hv : v ∈ R
  · have h := hy ⟨v, hv⟩ (mem_univ _)
    change LocalAdeles.diagonalLocal G v.val a * LocalAdeles.diagonalLocal G v.val b.val ∈ localAdelicTarget G T U v at h
    simpa only [map_mul] using h
  · have hvT : v ∉ T := fun h => hv (hTR h)
    rw [localAdelicTarget, ite_eq_right hvT, map_mul]
    exact (LocalAdeles.integralLocalSubgroup G v.val).mul_mem (haR v hv) (b.property v hv)

end

/-! Strong approximation reduces to finite invariant arithmetic
volume, additive generation outside a finite exceptional set, and
ordinary weak approximation at those exceptional places. -/

open scoped Classical _root_.NumberField
open Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem strongApproximation_of_finiteIndex_exceptional_weakApproximation
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (hindex : ∀ T : Finset (ApproximationTopology.AwayPlace S), (Groups.arithmeticProjection G S T).range.topologicalClosure.FiniteIndex)
    (B : Finset (ApproximationTopology.AwayPlace S))
    (hweak : DenseRange (fun g : G.RationalPoints => fun v : (B : Set (ApproximationTopology.AwayPlace S)) =>
      LocalAdeles.diagonalLocal G v.val.val g))
    (hgen : ∀ v : ApproximationTopology.AwayPlace S, v ∉ B → localAdditiveGeneration G v.val) :
    DenseRange (LocalAdeles.diagonalAway G S) := by
  apply (ApproximationTopology.denseRange_diagonalAway_iff G S).mpr
  intro T U hU hne
  obtain ⟨a, haB⟩ := exceptional_weakApproximation_point G S B T hweak U hU hne
  obtain ⟨D, haD⟩ := rational_point_finite_denominators G S a
  let R := T ∪ D
  have hTR : T ⊆ R := Finset.subset_union_left
  have haR : ∀ v : ApproximationTopology.AwayPlace S, v ∉ R →
      LocalAdeles.diagonalLocal G v.val a ∈ LocalAdeles.integralLocalSubgroup G v.val := by
    intro v hv
    exact haD v (fun h => hv (Finset.mem_union_right T h))
  obtain ⟨g, hg⟩ := arithmetic_correction_of_finiteIndex G S B T R hTR (hindex R)
    hgen U hU hne a haB haR
  refine ⟨g, ?_, ?_⟩
  · intro v hv
    simpa only [localAdelicTarget, ite_eq_left hv, LocalAdeles.diagonalAway_apply] using hg v
  · intro v hv
    simpa only [localAdelicTarget, ite_eq_right hv, LocalAdeles.diagonalAway_apply] using! hg v

theorem strongApproximation_of_volume_and_local_generation
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hconn : G.IsGeometricallyConnected)
    (hsimple : AlgebraicHypotheses.IsAbsolutelyAlmostSimple G) (hsemi : G.IsSemisimple)
    (S : Finset (LocalAdeles.Place F)) (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S)
    (hnoncompact : ∃ w : LocalAdeles.Place F, w ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints G w))
    (hvolume : ∀ T : Finset (ApproximationTopology.AwayPlace S), CompactQuotientProjection.QuotientHasInvariantProbability (Ambient.arithmeticAmbientSubgroup G S T))
    (B : Finset (ApproximationTopology.AwayPlace S))
    (hweak : DenseRange (fun g : G.RationalPoints => fun v : (B : Set (ApproximationTopology.AwayPlace S)) =>
      LocalAdeles.diagonalLocal G v.val.val g))
    (hgen : ∀ v : ApproximationTopology.AwayPlace S, v ∉ B → localAdditiveGeneration G v.val) :
    DenseRange (LocalAdeles.diagonalAway G S) :=
  strongApproximation_of_finiteIndex_exceptional_weakApproximation G S
    (SelectedArithmeticProduct.arithmeticProjection_closure_finiteIndex_of_volume G hconn hsimple hsemi S harch hnoncompact hvolume)
    B hweak hgen

end

end OAI.NumberTheory.Quaternion.Arithmetic.ExceptionalApproximation
