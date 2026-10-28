import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Subfunctor.Basic

/-! # Open Unit Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.OpenUnitLocus

noncomputable section

/-!
The unit locus of a global section is represented by its principal open.
This provides the geometric open domains for Grassmannian chart transitions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe u

theorem isUnit_iff_basicOpen_eq_top (X : Scheme.{u}) (s : Γ(X, ⊤)) :
    IsUnit s ↔ X.basicOpen s = ⊤ := by
  constructor
  · exact X.basicOpen_of_isUnit
  · intro h
    apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ s
    intro x hx
    apply (Scheme.mem_basicOpen X s x hx).mp
    rw [h]
    trivial

theorem isUnit_appTop_iff_range_subset {T X : Scheme.{u}}
    (f : T ⟶ X) (s : Γ(X, ⊤)) :
    IsUnit (f.appTop s) ↔ Set.range f ⊆ (X.basicOpen s : Set X) := by
  rw [isUnit_iff_basicOpen_eq_top, ← Scheme.preimage_basicOpen_top]
  constructor
  · intro h x hx
    obtain ⟨t, rfl⟩ := hx
    change t ∈ f ⁻¹ᵁ X.basicOpen s
    rw [h]
    trivial
  · intro h
    apply top_unique
    intro t _
    exact h ⟨t, rfl⟩

/-- The condition that a section becomes invertible after pullback. -/
def unitSubfunctor (X : Scheme.{u}) (s : Γ(X, ⊤)) : Subfunctor (yoneda.obj X) where
  obj T := {f | IsUnit (f.appTop s)}
  map a f hf := by
    change IsUnit ((a.unop ≫ f).appTop s)
    exact hf.map a.unop.appTop.hom

/-- Principal opens represent invertibility conditions over every test scheme. -/
theorem unit_locus_representable (X : Scheme.{u}) (s : Γ(X, ⊤)) :
    ∃ (U : Scheme.{u}) (j : U ⟶ X), IsOpenImmersion j ∧
      ∃ e : yoneda.obj U ≅ (unitSubfunctor X s).toFunctor,
        e.hom ≫ (unitSubfunctor X s).ι = yoneda.map j := by
  let U : X.Opens := X.basicOpen s
  let j : U.toScheme ⟶ X := U.ι
  have hj : IsUnit (j.appTop s) := by
    apply (isUnit_appTop_iff_range_subset j s).mpr
    change Set.range U.ι ⊆ (U : Set X)
    rw [Scheme.Opens.range_ι]
  let t : yoneda.obj U.toScheme ⟶ (unitSubfunctor X s).toFunctor :=
    { app := fun T => ↾fun y => ⟨y ≫ j, hj.map y.appTop.hom⟩
      naturality := by
        intro T V a
        apply ConcreteCategory.hom_ext
        intro y
        apply Subtype.ext
        exact Category.assoc _ _ _ }
  have : IsIso t := by
    apply (NatTrans.isIso_iff_isIso_app t).mpr
    intro T
    apply (isIso_iff_bijective (t.app T)).mpr
    constructor
    · intro y z h
      apply (cancel_mono j).mp
      exact congrArg Subtype.val h
    · intro x
      let f : T.unop ⟶ X := x.val
      have hx : Set.range f ⊆ Set.range j := by
        change Set.range f ⊆ Set.range U.ι
        rw [Scheme.Opens.range_ι]
        exact (isUnit_appTop_iff_range_subset f s).mp x.property
      exact ⟨IsOpenImmersion.lift j f hx,
        Subtype.ext (IsOpenImmersion.lift_fac j f hx)⟩
  exact ⟨U.toScheme, j, inferInstance, asIso t, rfl⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.OpenUnitLocus
