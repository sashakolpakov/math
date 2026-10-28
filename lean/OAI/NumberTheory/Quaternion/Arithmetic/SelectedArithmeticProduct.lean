import OAI.NumberTheory.Quaternion.Arithmetic.OpennessOfVolume
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Selected Arithmetic Product -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SelectedArithmeticProduct

noncomputable section

section

/-! Reindex the actual selected-place product by finite places once
the omitted set contains every archimedean place. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def awayFinitePlace (S : Finset (LocalAdeles.Place F))
    (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) (v : ApproximationTopology.AwayPlace S) :
    HeightOneSpectrum (𝓞 F) := by
  obtain ⟨v, hv⟩ := v
  cases v with
  | inl w => exact (hv (harch w)).elim
  | inr w => exact w

omit [NumberField F] in
theorem inr_awayFinitePlace (S : Finset (LocalAdeles.Place F))
    (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) (v : ApproximationTopology.AwayPlace S) :
    Sum.inr (awayFinitePlace S harch v) = v.val := by
  obtain ⟨v, hv⟩ := v
  cases v with
  | inl w => exact (hv (harch w)).elim
  | inr w => rfl

def localPointsPlaceEquiv (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) {v w : LocalAdeles.Place F} (h : v = w) :
    LocalAdeles.LocalPoints G v ≃ₜ* LocalAdeles.LocalPoints G w := by
  subst w
  exact ContinuousMulEquiv.refl _

theorem localPointsPlaceEquiv_diagonal (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) {v w : LocalAdeles.Place F} (h : v = w)
    (g : G.RationalPoints) : localPointsPlaceEquiv G h (LocalAdeles.diagonalLocal G v g) = LocalAdeles.diagonalLocal G w g := by
  subst w
  rfl

def selectedFinitePlaces (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S))
    (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) :
    ↥(T : Set (ApproximationTopology.AwayPlace S)) → HeightOneSpectrum (𝓞 F) :=
  fun v => awayFinitePlace S harch v.val

omit [NumberField F] in
theorem selectedFinitePlaces_injective (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S))
    (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) :
    Function.Injective (selectedFinitePlaces S T harch) := by
  intro v w h
  apply Subtype.ext
  apply Subtype.ext
  rw [← inr_awayFinitePlace S harch v.val, ← inr_awayFinitePlace S harch w.val]
  exact congrArg Sum.inr h

def selectedFiniteProductEquiv (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (T : Finset (ApproximationTopology.AwayPlace S)) (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) :
    Groups.SelectedLocalProduct G S T ≃ₜ*
      (∀ v : (T : Set (ApproximationTopology.AwayPlace S)), LocalAdeles.LocalPoints G (Sum.inr (selectedFinitePlaces S T harch v))) :=
  ContinuousMulEquiv.mk'
    (Homeomorph.piCongrRight (fun v : (T : Set (ApproximationTopology.AwayPlace S)) =>
      (localPointsPlaceEquiv G (inr_awayFinitePlace S harch v.val).symm).toHomeomorph))
    (fun x y => funext fun v => map_mul (localPointsPlaceEquiv G
      (inr_awayFinitePlace S harch v.val).symm) (x v) (y v))

theorem selectedFiniteProductEquiv_projection (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S))
    (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) (g : Groups.arithmeticSubgroup G S T) :
    selectedFiniteProductEquiv G S T harch (Groups.arithmeticProjection G S T g) =
      Product.diagonalFiniteProduct G (selectedFinitePlaces S T harch) g.val := by
  funext v
  exact localPointsPlaceEquiv_diagonal G (inr_awayFinitePlace S harch v.val).symm g.val

end

section

/-! The selected arithmetic projection is exactly the reindexed
finite-place arithmetic subgroup, with the same integrality conditions. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def selectedArithmeticPlaces (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S)) : Finset (LocalAdeles.Place F) :=
  S ∪ T.image Subtype.val

theorem arithmeticSubgroup_eq_selectedIntegral (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S)) :
    Groups.arithmeticSubgroup G S T = Groups.sIntegralPoints G (selectedArithmeticPlaces S T : Set (LocalAdeles.Place F)) := by
  rw [Groups.arithmeticSubgroup_eq_sIntegralPoints]
  congr 1
  simp only [selectedArithmeticPlaces, Finset.coe_union, Finset.coe_image]

theorem selectedFiniteProductEquiv_arithmetic_range (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S))
    (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) :
    (Groups.arithmeticProjection G S T).range.map (selectedFiniteProductEquiv G S T harch).toMulEquiv.toMonoidHom =
      Product.arithmeticProductSubgroup G (selectedArithmeticPlaces S T) (selectedFinitePlaces S T harch) := by
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
    refine ⟨g.val, ?_, (selectedFiniteProductEquiv_projection G S T harch g).symm⟩
    exact (arithmeticSubgroup_eq_selectedIntegral G S T).le g.property
  · rintro ⟨g, hg, rfl⟩
    have hg' : g ∈ Groups.arithmeticSubgroup G S T :=
      (arithmeticSubgroup_eq_selectedIntegral G S T).ge hg
    refine ⟨Groups.arithmeticProjection G S T ⟨g, hg'⟩, ⟨⟨g, hg'⟩, rfl⟩, ?_⟩
    exact selectedFiniteProductEquiv_projection G S T harch ⟨g, hg'⟩

end

/-! The actual selected arithmetic projection has open closure, and
then finite index, from the remaining invariant-volume obligation. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

theorem subgroup_closure_isOpen_of_equiv_map
    {L M : Type*} [Group L] [Group M] [TopologicalSpace L] [TopologicalSpace M]
    [IsTopologicalGroup L] [IsTopologicalGroup M]
    (e : L ≃ₜ* M) (H : Subgroup L)
    (hopen : IsOpen ((H.map e.toMulEquiv.toMonoidHom).topologicalClosure : Set M)) :
    IsOpen (H.topologicalClosure : Set L) := by
  have he : (H.topologicalClosure : Set L) =
      e ⁻¹' ((H.map e.toMulEquiv.toMonoidHom).topologicalClosure : Set M) := by
    change closure (H : Set L) = e ⁻¹' closure (e '' (H : Set L))
    apply Eq.trans ?_ (e.toHomeomorph.preimage_closure (e '' (H : Set L))).symm
    congr 1
    exact (Set.preimage_image_eq _ e.injective).symm
  rw [he]
  exact hopen.preimage e.continuous

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem arithmeticProjection_closure_isOpen_of_volume
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hconn : G.IsGeometricallyConnected)
    (hsimple : AlgebraicHypotheses.IsAbsolutelyAlmostSimple G) (hsemi : G.IsSemisimple)
    (S : Finset (LocalAdeles.Place F)) (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S)
    (hnoncompact : ∃ w : LocalAdeles.Place F, w ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints G w))
    (hvolume : ∀ v : ApproximationTopology.AwayPlace S, CompactQuotientProjection.QuotientHasInvariantProbability (Ambient.arithmeticAmbientSubgroup G S {v}))
    (T : Finset (ApproximationTopology.AwayPlace S)) :
    IsOpen ((Groups.arithmeticProjection G S T).range.topologicalClosure : Set (Groups.SelectedLocalProduct G S T)) := by
  let v := selectedFinitePlaces S T harch
  have haway (i : (T : Set (ApproximationTopology.AwayPlace S))) : Sum.inr (v i) ∉ S := by
    change Sum.inr (awayFinitePlace S harch i.val) ∉ S
    rw [inr_awayFinitePlace]
    exact i.val.property
  have hSU : S ⊆ selectedArithmeticPlaces S T := Finset.subset_union_left
  have hU (i : (T : Set (ApproximationTopology.AwayPlace S))) : Sum.inr (v i) ∈ selectedArithmeticPlaces S T := by
    change Sum.inr (awayFinitePlace S harch i.val) ∈ selectedArithmeticPlaces S T
    rw [inr_awayFinitePlace]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩)
  have hopen := OpennessOfVolume.arithmetic_finite_product_closure_isOpen_of_volume G hconn hsimple hsemi
    S (selectedArithmeticPlaces S T) harch v (selectedFinitePlaces_injective S T harch)
    haway hSU hU hnoncompact (fun i => hvolume ⟨Sum.inr (v i), haway i⟩)
  apply subgroup_closure_isOpen_of_equiv_map (selectedFiniteProductEquiv G S T harch)
    (Groups.arithmeticProjection G S T).range
  rwa [selectedFiniteProductEquiv_arithmetic_range]

theorem arithmeticProjection_closure_finiteIndex_of_volume
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hconn : G.IsGeometricallyConnected)
    (hsimple : AlgebraicHypotheses.IsAbsolutelyAlmostSimple G) (hsemi : G.IsSemisimple)
    (S : Finset (LocalAdeles.Place F)) (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S)
    (hnoncompact : ∃ w : LocalAdeles.Place F, w ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints G w))
    (hvolume : ∀ T : Finset (ApproximationTopology.AwayPlace S), CompactQuotientProjection.QuotientHasInvariantProbability (Ambient.arithmeticAmbientSubgroup G S T))
    (T : Finset (ApproximationTopology.AwayPlace S)) : (Groups.arithmeticProjection G S T).range.topologicalClosure.FiniteIndex :=
  Ambient.arithmeticProjection_closure_finiteIndex G S T (hvolume T)
    (arithmeticProjection_closure_isOpen_of_volume G hconn hsimple hsemi S harch hnoncompact
      (fun v => hvolume {v}) T)

end

end OAI.NumberTheory.Quaternion.Arithmetic.SelectedArithmeticProduct
