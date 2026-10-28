import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Order.WellFounded

/-! # Finite Endomorphism -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteEndomorphism.Construction

noncomputable section

/-! Surjectivity of finite endomorphisms of integral Noetherian schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- Quasi-finite morphisms do not identify distinct comparable points. -/
theorem eq_of_specializes_of_eq_image
    {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f]
    {x y : X} (hxy : x ⤳ y) (heq : f x = f y) : x = y :=
  (f.isDiscrete_preimage_singleton (f x)).eq_of_specializes hxy rfl heq.symm

/-- A quasi-finite morphism strictly preserves the specialization order. -/
theorem strictMono_of_locallyQuasiFinite
    {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f] : StrictMono f := by
  intro x y hxy
  have hle : f x ≤ f y :=
    Scheme.le_iff_specializes.mpr ((Scheme.le_iff_specializes.mp hxy.le).map f.continuous)
  apply lt_iff_le_not_ge.mpr
  refine ⟨hle, ?_⟩
  intro hge
  have heq : f x = f y := ((Scheme.le_iff_specializes.mp hge).antisymm
    (Scheme.le_iff_specializes.mp hle)).eq
  have hxy' : y = x := eq_of_specializes_of_eq_image f
    (Scheme.le_iff_specializes.mp hxy.le) heq.symm
  exact hxy.not_ge (le_of_eq hxy')

/-- The specialization order of a Noetherian scheme has no infinite
strictly descending chains, since point closures are closed subsets. -/
theorem wellFoundedLT_of_noetherian_scheme (X : Scheme) [NoetherianSpace X] :
    WellFoundedLT X := by
  let c : X ↪o Closeds X :=
    { toFun := fun x => ⟨closure {x}, isClosed_closure⟩
      inj' := fun x y h => by
        have hxy : closure ({x} : Set X) = closure {y} := congrArg SetLike.coe h
        exact ((specializes_iff_closure_subset.mpr hxy.ge).antisymm
          (specializes_iff_closure_subset.mpr hxy.le)).eq
      map_rel_iff' := by
        intro x y
        exact specializes_iff_closure_subset.symm }
  exact c.strictMono.wellFoundedLT

/-- A finite endomorphism of an integral Noetherian scheme is surjective.
Its image contains the generic point: otherwise its iterates would yield
an infinite descending chain in the specialization order. -/
theorem surjective_finite_endomorphism_of_isIntegral
    {X : Scheme} [IsIntegral X] [NoetherianSpace X]
    (f : X ⟶ X) [IsFinite f] : Surjective f := by
  have : WellFoundedLT X := wellFoundedLT_of_noetherian_scheme X
  have hf : StrictMono f := strictMono_of_locallyQuasiFinite f
  have hnot : ¬ f (⊤ : X) < ⊤ := by
    intro h
    obtain ⟨x, hx, hmin⟩ := wellFounded_lt.has_min {x : X | f x < x} ⟨⊤, h⟩
    exact hmin (f x) (hf hx) hx
  have hge : (⊤ : X) ≤ f ⊤ := by
    by_contra h
    exact hnot (lt_iff_le_not_ge.mpr ⟨le_top, h⟩)
  have htop : f (⊤ : X) = ⊤ := ((Scheme.le_iff_specializes.mp hge).antisymm
    (genericPoint_specializes (f ⊤))).eq
  have hclosed : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  refine ⟨fun x => ?_⟩
  exact (genericPoint_specializes x).mem_closed hclosed ⟨⊤, htop⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteEndomorphism.Construction
