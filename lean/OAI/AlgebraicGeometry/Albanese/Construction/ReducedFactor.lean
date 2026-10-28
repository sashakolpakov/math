import OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Reduced Factor -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.ReducedFactor

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- For a reduced source, set-theoretic containment in a closed subscheme
implies the ideal-sheaf containment needed for an algebraic factorization. -/
theorem ker_le_of_range_subset {X Y Z : Scheme.{u}}
    (i : X ⟶ Z) [IsClosedImmersion i] (f : Y ⟶ Z) [IsReduced Y]
    (h : Set.range f ⊆ Set.range i) : i.ker ≤ f.ker := by
  rw [← Scheme.IdealSheafData.map_bot f, Scheme.IdealSheafData.le_map_iff_comap_le]
  apply le_of_eq
  apply Scheme.IdealSheafData.support_eq_top_iff.mp
  rw [Scheme.IdealSheafData.support_comap]
  ext y
  simp only [TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage,
    TopologicalSpace.Closeds.coe_top, Set.mem_univ, iff_true]
  exact i.range_subset_ker_support (h ⟨y, rfl⟩)

/-- The unique algebraic factorization through a closed subscheme for a
reduced source whose points all land in that subscheme. -/
def factorThroughClosed {X Y Z : Scheme.{u}}
    (i : X ⟶ Z) [IsClosedImmersion i] (f : Y ⟶ Z) [IsReduced Y]
    (h : Set.range f ⊆ Set.range i) : Y ⟶ X :=
  IsClosedImmersion.lift i f (ker_le_of_range_subset i f h)

@[reassoc (attr := simp)]
theorem factorThroughClosed_comp {X Y Z : Scheme.{u}}
    (i : X ⟶ Z) [IsClosedImmersion i] (f : Y ⟶ Z) [IsReduced Y]
    (h : Set.range f ⊆ Set.range i) : factorThroughClosed i f h ≫ i = f :=
  IsClosedImmersion.lift_fac i f (ker_le_of_range_subset i f h)

/-- A closed target condition on a finite-type source can be checked on all
rational points over an algebraically closed field. -/
theorem range_subset_closed_of_points {K : Type u} [Field K] [IsAlgClosed K]
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    (f : X ⟶ Y) (Z : TopologicalSpace.Closeds Y.left)
    (h : ∀ p : Over.mk (𝟙 (Spec (.of K))) ⟶ X,
      (p ≫ f).left (IsLocalRing.closedPoint K) ∈ Z) :
    Set.range f.left ⊆ Z := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hclosed : IsClosed (f.left ⁻¹' (Z : Set Y.left)) :=
    Z.isClosed.preimage f.left.continuous
  have hpoints : closedPoints X.left ⊆ f.left ⁻¹' (Z : Set Y.left) := by
    intro x hx
    change IsClosed {x} at hx
    let p : Over.mk (𝟙 (Spec (.of K))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)
    have hp : (p ≫ f).left (IsLocalRing.closedPoint K) = f.left x :=
      congrArg f.left (pointOfClosedPoint_apply X.hom x hx (IsLocalRing.closedPoint K))
    change f.left x ∈ Z
    rw [← hp]
    exact h p
  rintro y ⟨x, rfl⟩
  have hx : x ∈ closure (closedPoints X.left) := by rw [closure_closedPoints]; trivial
  exact hclosed.closure_subset_iff.mpr hpoints hx

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A reduced finite-type scheme with a transitive action by its algebraic
automorphisms on rational points is smooth over an algebraically closed field. -/
theorem smooth_of_point_transitive {K : Type u} [Field K] [IsAlgClosed K]
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [IsReduced X.left] [Nonempty X.left]
    (htrans : ∀ p q : Over.mk (𝟙 (Spec (.of K))) ⟶ X,
      ∃ e : X ≅ X, p ≫ e.hom = q) : Smooth X.hom := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro hbad
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hbad
    X.hom.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints
    X.hom.dense_smoothLocus_of_perfectField.nonempty X.hom.smoothLocus.2.isLocallyClosed
  let p : Over.mk (𝟙 (Spec (.of K))) ⟶ X :=
    Over.homMk _ ((pointEquivClosedPoint X.hom).symm ⟨x, hxc⟩).2
  let q : Over.mk (𝟙 (Spec (.of K))) ⟶ X :=
    Over.homMk _ ((pointEquivClosedPoint X.hom).symm ⟨y, hyc⟩).2
  obtain ⟨e, he⟩ := htrans p q
  have hexy : e.hom.left x = y := by
    simpa [p, q, pointEquivClosedPoint] using congr(($he).left (IsLocalRing.closedPoint K))
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hxpre : x ∈ e.hom.left ⁻¹ᵁ X.hom.smoothLocus := by
    change e.hom.left x ∈ X.hom.smoothLocus
    rw [hexy]
    exact hy
  rw! [Scheme.Hom.preimage_smoothLocus_eq, e.hom.w] at hxpre
  exact hx hxpre

end

end OAI.AlgebraicGeometry.Albanese.Construction.ReducedFactor
