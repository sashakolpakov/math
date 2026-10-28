import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Jacobson.Ideal

/-! # Closed Stalk Jacobson -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.ClosedStalkJacobson

noncomputable section

/-! At a closed point of a proper source, the image of the base
Jacobson radical lies in the maximal ideal of the source stalk. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (R : CommRingCat.{u}) {X : Scheme.{u}} (f : X ⟶ Spec R) [IsProper f]

theorem proper_closed_stalk_jacobson (x : X) (hx : IsClosed ({x} : Set X))
    (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) :
    I.map (Spec.preimage (X.fromSpecStalk x ≫ f)).hom ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  let A := X.presheaf.stalk x
  let φ : R ⟶ A := Spec.preimage (X.fromSpecStalk x ≫ f)
  have he : Spec.map φ (IsLocalRing.closedPoint A) = f x := by
    have hφ : Spec.map φ = X.fromSpecStalk x ≫ f := Spec.map_preimage _
    erw [hφ, Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
  have hfx : IsClosed ({f x} : Set (Spec R)) := by
    simpa only [Set.image_singleton] using f.isClosedMap {x} hx
  have hm : (Ideal.comap φ.hom (IsLocalRing.maximalIdeal A)).IsMaximal := by
    apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal
      (PrimeSpectrum.comap φ.hom (IsLocalRing.closedPoint A))).mp
    change IsClosed ({Spec.map φ (IsLocalRing.closedPoint A)} : Set (Spec R))
    rwa [he]
  apply Ideal.map_le_iff_le_comap.mpr
  apply hI.trans
  exact (Ideal.jacobson_mono (bot_le : (⊥ : Ideal R) ≤
    (IsLocalRing.maximalIdeal A).comap φ.hom)).trans_eq
      (@Ideal.jacobson_eq_self_of_isMaximal R _ _ hm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.ClosedStalkJacobson
