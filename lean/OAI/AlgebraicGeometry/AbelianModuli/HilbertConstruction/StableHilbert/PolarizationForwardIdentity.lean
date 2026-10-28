import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationForwardExistence

/-! # Polarization Forward Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationForwardIdentity

noncomputable section

/-! The existential forward construction is the original pullback lift:
the second projection is monic, so its base equation determines it. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe v u

def pullbackLiftFromExists
    {C : Type u} [Category.{v} C] {T X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] (b : T ⟶ Y)
    (h : ∃ a : T ⟶ X, a ≫ f = b ≫ g) : T ⟶ pullback f g :=
  pullback.lift h.choose b h.choose_spec

theorem pullbackLiftFromExists_snd
    {C : Type u} [Category.{v} C] {T X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] (b : T ⟶ Y)
    (h : ∃ a : T ⟶ X, a ≫ f = b ≫ g) :
    pullbackLiftFromExists f g b h ≫ pullback.snd f g = b :=
  pullback.lift_snd _ _ _

theorem eq_pullbackLiftFromExists
    {C : Type u} [Category.{v} C] {T X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [Mono f] (b : T ⟶ Y)
    (h : ∃ a : T ⟶ X, a ≫ f = b ≫ g)
    (e : T ⟶ pullback f g) (he : e ≫ pullback.snd f g = b) :
    e = pullbackLiftFromExists f g b h :=
  (cancel_mono (pullback.snd f g)).mp (he.trans (pullbackLiftFromExists_snd f g b h).symm)

namespace StableHilbertPolarizationTransition
variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)

theorem forwardOfExists_eq_originalLift :
    PolarizationForwardExistence.StableHilbertPolarizationTransition.forwardOfExists R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k =
      pullbackLiftFromExists
        (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)
        (PolarizationTransitionBases.StableHilbertPolarizationTransition.rightBaseMap R i D H hH hD g Hm Hi N labels j k)
        (pullback.snd (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)
          (PolarizationTransitionBases.StableHilbertPolarizationTransition.leftBaseMap R i D H hH hD g Hm Hi N labels j k))
        (PolarizationForwardExistence.StableHilbertPolarizationTransition.rightLift R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k) :=
  eq_pullbackLiftFromExists
    (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)
    (PolarizationTransitionBases.StableHilbertPolarizationTransition.rightBaseMap R i D H hH hD g Hm Hi N labels j k)
    (pullback.snd (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)
      (PolarizationTransitionBases.StableHilbertPolarizationTransition.leftBaseMap R i D H hH hD g Hm Hi N labels j k))
    (PolarizationForwardExistence.StableHilbertPolarizationTransition.rightLift R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (PolarizationForwardExistence.StableHilbertPolarizationTransition.forwardOfExists R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (PolarizationForwardExistence.StableHilbertPolarizationTransition.forwardOfExists_base R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)

end StableHilbertPolarizationTransition

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationForwardIdentity
