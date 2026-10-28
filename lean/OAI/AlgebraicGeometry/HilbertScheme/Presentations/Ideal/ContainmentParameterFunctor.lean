import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientCover
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentOpenLocality
import Mathlib.CategoryTheory.Subfunctor.Basic

/-! # Containment Parameter Functor -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentParameterFunctor.Hilbert

noncomputable section

/-! Scheme-theoretic containment of two universal ambient ideals is a
natural condition on parameter maps and is local on the test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X : Over S) {B : Over S}
variable (I J : (Hilbert.Functor.ambient X B).IdealSheafData)

def idealContainmentParameterSubfunctor : Subfunctor (yoneda.obj B) where
  obj T := {x | I.comap (Hilbert.Functor.ambientMap X x) ≤ J.comap (Hilbert.Functor.ambientMap X x)}
  map f x hx := by
    change I.comap (Hilbert.Functor.ambientMap X (f.unop ≫ x)) ≤ J.comap (Hilbert.Functor.ambientMap X (f.unop ≫ x))
    rw [Hilbert.Functor.ambientMap_comp, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact Scheme.IdealSheafData.comap_mono (Hilbert.Functor.ambientMap X f.unop) hx

theorem idealContainmentParameter_mem {T : Over S} (x : T ⟶ B) :
    x ∈ (idealContainmentParameterSubfunctor X I J).obj (.op T) ↔
      I.comap (Hilbert.Functor.ambientMap X x) ≤ J.comap (Hilbert.Functor.ambientMap X x) := Iff.rfl

variable {T : Over S} {ι : Type u} (U : ι → Over S) (f : ∀ i, U i ⟶ T)
variable [∀ i, IsOpenImmersion (f i).left]
variable (hcover : ∀ t : T.left, ∃ i, ∃ u : (U i).left, (f i).left u = t)

include hcover in
theorem idealContainmentParameter_of_openCover (x : T ⟶ B)
    (h : ∀ i, f i ≫ x ∈ (idealContainmentParameterSubfunctor X I J).obj (.op (U i))) :
    x ∈ (idealContainmentParameterSubfunctor X I J).obj (.op T) := by
  apply ContainmentOpenLocality.ideal_le_of_openCover (Hilbert.AmbientCover.ambientOpenCover X U f hcover)
  intro i
  change (I.comap (Hilbert.Functor.ambientMap X x)).comap (Hilbert.Functor.ambientMap X (f i)) ≤
    (J.comap (Hilbert.Functor.ambientMap X x)).comap (Hilbert.Functor.ambientMap X (f i))
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, ← Hilbert.Functor.ambientMap_comp]
  exact h i

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentParameterFunctor.Hilbert
