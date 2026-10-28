import OAI.AlgebraicTopology.Cohomology.Singular.Contractible
import OAI.AlgebraicTopology.Cohomology.Singular.Augmentation
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

/-! # One Primitives -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives

noncomputable section

/-!
# DegreeTwo: normalized primitives of actual singular one-cocycles

On a contractible space, a one-cocycle has a zero-cochain primitive. Fixing its
value at one point removes the constant ambiguity, so the primitive depends
linearly on the cocycle. This is the source of the period homomorphism on a
lattice covering.
-/

open _root_.CategoryTheory

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0})

/-- Equal coboundaries make the difference of point functions constant. -/
theorem difference_point_value [PathConnectedSpace X]
    (a b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X 0)
    (hd : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d 0 1 a = (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d 0 1 b)
    (x y : X) :
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).hom a x - (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).hom b x =
      (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).hom a y - (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).hom b y := by
  have hz : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d 0 1 (a - b) = 0 := by
    rw [map_sub, hd, sub_self]
  have h := (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCoboundary_eq_zero_iff M X (a - b)).mp hz x y
    (PathConnectedSpace.joined x y)
  simpa only [map_sub, Pi.sub_apply] using h

/-- On a path-connected space, a zero-cochain with zero coboundary is
determined by its value at a single point. -/
theorem zeroCochain_eq_of_d_eq [PathConnectedSpace X]
    (x₀ : X) (a b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X 0)
    (hd : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d 0 1 a = (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d 0 1 b)
    (h₀ : (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).hom a x₀ =
      (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).hom b x₀) : a = b := by
  have hz : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d 0 1 (a - b) = 0 := by
    rw [map_sub, hd, sub_self]
  have hp := (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCoboundary_eq_zero_iff M X (a - b)).mp hz
  apply (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).toLinearEquiv.injective
  ext x
  have h := hp x₀ x (PathConnectedSpace.joined x₀ x)
  simp only [map_sub, Pi.sub_apply, h₀, sub_self] at h
  exact sub_eq_zero.mp h.symm

/-- Every actual singular one-cocycle has a unique primitive normalized at
the chosen point of a contractible space. -/
theorem existsUnique_normalizedPrimitive [ContractibleSpace X] (x₀ : X)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M X 1) :
    ∃! b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X 0,
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d 0 1 b = c.1 ∧
      (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).hom b x₀ = 0 := by
  obtain ⟨b, hb⟩ := AlgebraicTopology.Cohomology.Singular.Contractible.exists_singularPrimitive_of_contractible M X 0 c
  let a : LocallyConstant X M :=
    LocallyConstant.const X ((AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).hom b x₀)
  let k := AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero M X a
  have hk : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d 0 1 k = 0 := by
    apply (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCoboundary_eq_zero_iff M X k).mpr
    intro x y _
    change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).hom
        (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero M X a) x =
      (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).hom (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero M X a) y
    rw [AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_apply, AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_apply]
    rfl
  have hd : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d 0 1 (b - k) = c.1 := by
    rw [map_sub, hb, hk, sub_zero]
  have h₀ : (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).hom (b - k) x₀ = 0 := by
    rw [map_sub]
    change _ - (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).hom k x₀ = 0
    rw [AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_apply]
    exact sub_self _
  refine ⟨b - k, ⟨hd, h₀⟩, ?_⟩
  intro b' hb'
  exact zeroCochain_eq_of_d_eq M X x₀ b' (b - k)
    (hb'.1.trans hd.symm) (hb'.2.trans h₀.symm)

variable [ContractibleSpace X] (x₀ : X)

/-- The canonical primitive after fixing its value at the basepoint. -/
def normalizedPrimitive (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M X 1) : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X 0 :=
  (existsUnique_normalizedPrimitive M X x₀ c).choose

theorem normalizedPrimitive_d (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M X 1) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d 0 1 (normalizedPrimitive M X x₀ c) = c.1 :=
  (existsUnique_normalizedPrimitive M X x₀ c).choose_spec.1.1

@[simp]
theorem normalizedPrimitive_at_basepoint (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M X 1) :
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).hom (normalizedPrimitive M X x₀ c) x₀ = 0 :=
  (existsUnique_normalizedPrimitive M X x₀ c).choose_spec.1.2

/-- Normalization makes the primitive operation genuinely linear. -/
def normalizedPrimitiveLinearMap :
    AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M X 1 →ₗ[R] (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X 0 where
  toFun := normalizedPrimitive M X x₀
  map_add' c d := by
    apply zeroCochain_eq_of_d_eq M X x₀
    · rw [map_add, normalizedPrimitive_d, normalizedPrimitive_d, normalizedPrimitive_d]
      rfl
    · simp only [map_add, Pi.add_apply]
      erw [normalizedPrimitive_at_basepoint, normalizedPrimitive_at_basepoint,
        normalizedPrimitive_at_basepoint]
      exact (add_zero 0).symm
  map_smul' r c := by
    apply zeroCochain_eq_of_d_eq M X x₀
    · rw [map_smul, normalizedPrimitive_d, normalizedPrimitive_d]
      rfl
    · simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
      erw [normalizedPrimitive_at_basepoint, normalizedPrimitive_at_basepoint]
      exact (smul_zero r).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives
