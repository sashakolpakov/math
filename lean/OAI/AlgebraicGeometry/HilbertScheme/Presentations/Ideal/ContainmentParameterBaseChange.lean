import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentParameterFunctor

/-! # Containment Parameter Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentParameterBaseChange.Hilbert

noncomputable section

/-! Restricting both universal ideals to a parameter chart gives
exactly the pullback of the original parameter-containment condition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X : Over S) {B U T : Over S}
variable (I J : (Hilbert.Functor.ambient X B).IdealSheafData) (b : U ⟶ B) (x : T ⟶ U)

theorem idealContainmentParameter_baseChange :
    x ∈ (ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X (I.comap (Hilbert.Functor.ambientMap X b))
      (J.comap (Hilbert.Functor.ambientMap X b))).obj (.op T) ↔
    x ≫ b ∈ (ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X I J).obj (.op T) := by
  change (I.comap (Hilbert.Functor.ambientMap X b)).comap (Hilbert.Functor.ambientMap X x) ≤
    (J.comap (Hilbert.Functor.ambientMap X b)).comap (Hilbert.Functor.ambientMap X x) ↔
      I.comap (Hilbert.Functor.ambientMap X (x ≫ b)) ≤ J.comap (Hilbert.Functor.ambientMap X (x ≫ b))
  rw [Hilbert.Functor.ambientMap_comp, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentParameterBaseChange.Hilbert
