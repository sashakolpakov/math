import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineNeighborhoodOpen
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Group Affine -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood

/-!
# Affine neighborhoods by group translations over an algebraically closed field

In an irreducible commutative algebraic group, a finite collection of rational
points fits in a translate of any nonempty affine open. The translation is
chosen from a finite intersection of nonempty open subsets of the group.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K]
variable (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]

noncomputable abbrev translate (a : 𝟙_ (Over (Spec (.of K))) ⟶ A) : A.left ≅ A.left :=
  (Over.forget (Spec (.of K))).mapIso (GrpObj.mulRight a)

omit [IsAlgClosed K] in
theorem exchange (a b : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    a.left ≫ (translate A b).hom = b.left ≫ (translate A a).hom := by
  change (a ≫ (GrpObj.mulRight b).hom).left = (b ≫ (GrpObj.mulRight a).hom).left
  apply congrArg (fun f : 𝟙_ (Over (Spec (.of K))) ⟶ A => f.left)
  change a ≫ (𝟙 A * (toUnit A ≫ b)) = b ≫ (𝟙 A * (toUnit A ≫ a))
  simp only [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    comp_toUnit, toUnit_unit, Category.id_comp]
  exact mul_comm a b

theorem exists_affineOpen_rationalPoints
    [LocallyOfFiniteType A.hom] [IrreducibleSpace A.left]
    {J : Type v} [Finite J] (a : J → (𝟙_ (Over (Spec (.of K))) ⟶ A))
    (U : A.left.Opens) (hU : IsAffineOpen U) (hne : (U : Set A.left).Nonempty) :
    ∃ V : A.left.Opens, IsAffineOpen V ∧
      ∀ i, (a i).left (IsLocalRing.closedPoint K) ∈ V := by
  classical
  let := Fintype.ofFinite J
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  let V : J → A.left.Opens := fun i => (translate A (a i)).hom ⁻¹ᵁ U
  let C : Finset (Set A.left) := Finset.univ.image (fun i => (V i : Set A.left))
  have hCopen : ∀ Z ∈ C, IsOpen Z := by
    intro Z hZ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hZ
    exact (V i).isOpen
  have hCne : ∀ Z ∈ C, (Set.univ ∩ Z).Nonempty := by
    intro Z hZ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hZ
    obtain ⟨x, hx⟩ := hne
    refine ⟨(translate A (a i)).inv x, trivial, ?_⟩
    change (translate A (a i)).hom ((translate A (a i)).inv x) ∈ U
    rw [Scheme.inv_hom_apply]
    exact hx
  have hC : (⋂₀ (C : Set (Set A.left))).Nonempty := by
    simpa only [Set.univ_inter] using isIrreducible_iff_sInter.mp
      (IrreducibleSpace.isIrreducible_univ A.left) C hCopen hCne
  obtain ⟨b₀, hb₀, hbclosed⟩ := nonempty_inter_closedPoints hC
    (C.finite_toSet.isOpen_sInter hCopen).isLocallyClosed
  let b : 𝟙_ (Over (Spec (.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom b₀ hbclosed) (pointOfClosedPoint_comp A.hom b₀ hbclosed)
  refine ⟨(translate A b).hom ⁻¹ᵁ U, hU.preimage_of_isIso _, ?_⟩
  intro i
  have hbV : b₀ ∈ V i := hb₀ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have he := congrArg (fun f : Spec (.of K) ⟶ A.left => f (IsLocalRing.closedPoint K))
    (exchange A (a i) b)
  change (translate A b).hom ((a i).left (IsLocalRing.closedPoint K)) ∈ U
  rw [show (translate A b).hom ((a i).left (IsLocalRing.closedPoint K)) =
      (translate A (a i)).hom (b.left (IsLocalRing.closedPoint K)) from he]
  have hb : b.left (IsLocalRing.closedPoint K) = b₀ :=
    pointOfClosedPoint_apply A.hom b₀ hbclosed _
  rw [hb]
  exact hbV

/-- Every finite set of points of an irreducible commutative algebraic group
over an algebraically closed field has one affine open neighborhood. -/
theorem exists_affineOpen_of_finite
    [LocallyOfFiniteType A.hom] [IrreducibleSpace A.left]
    (F : Set A.left) (hF : F.Finite) :
    ∃ U : A.left.Opens, IsAffineOpen U ∧ F ⊆ U := by
  classical
  let := hF.fintype
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have hc (x : F) : ∃ y : A.left, y ∈ closure ({x.val} : Set A.left) ∧ IsClosed {y} :=
    nonempty_inter_closedPoints (Set.singleton_nonempty x.val).closure
      isClosed_closure.isLocallyClosed
  choose y hy hyc using hc
  let p : F → (𝟙_ (Over (Spec (.of K))) ⟶ A) := fun x =>
    Over.homMk (pointOfClosedPoint A.hom (y x) (hyc x))
      (pointOfClosedPoint_comp A.hom (y x) (hyc x))
  let x₀ : A.left := Classical.choice inferInstance
  obtain ⟨U₀, hU₀, hx₀, _⟩ := Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens
    (show x₀ ∈ (⊤ : A.left.Opens) from trivial)
  let U : A.left.Opens := U₀
  obtain ⟨V, hV, hpV⟩ := exists_affineOpen_rationalPoints A p U hU₀ ⟨x₀, hx₀⟩
  refine ⟨V, hV, ?_⟩
  intro x hx
  apply (specializes_iff_mem_closure.mpr (hy ⟨x, hx⟩)).mem_open V.isOpen
  have hp : (p ⟨x, hx⟩).left (IsLocalRing.closedPoint K) = y ⟨x, hx⟩ :=
    pointOfClosedPoint_apply A.hom (y ⟨x, hx⟩) (hyc ⟨x, hx⟩) _
  exact hp ▸ hpV ⟨x, hx⟩

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood
