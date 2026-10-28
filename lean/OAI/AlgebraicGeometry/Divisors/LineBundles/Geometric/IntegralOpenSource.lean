import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Integral Open Source -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.IntegralOpenSource.BundleCycles

noncomputable section

section

/-! Restricting the source of a geometrically integral morphism to an open
that still surjects onto the base preserves geometrically integral fibers. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem geometricallyIntegral_openSource {E X U : Scheme.{0}}
    (p : E ⟶ X) [GeometricallyIntegral p] (j : U ⟶ E) [IsOpenImmersion j]
    [Surjective (j ≫ p)] : GeometricallyIntegral (j ≫ p) := by
  constructor
  intro K _ t V a b h
  have : Surjective b := MorphismProperty.of_isPullback h inferInstance
  have : Nonempty V := by
    obtain ⟨v, _⟩ := b.surjective (Classical.choice (inferInstance : Nonempty (Spec (.of K))))
    exact ⟨v⟩
  have : IsIntegral (pullback p t) := GeometricallyIntegral.geometrically_isIntegral
    t (pullback.fst p t) (pullback.snd p t) (IsPullback.of_hasPullback p t)
  let i : V ⟶ pullback p t := pullback.lift (a ≫ j) b
    (by simpa only [Category.assoc] using h.w)
  have ho : IsPullback a (i ≫ pullback.snd p t) (j ≫ p) t := by
    simpa only [i, pullback.lift_snd] using h
  have hi : IsPullback a i j (pullback.fst p t) :=
    IsPullback.of_bot ho (by simp only [i, pullback.lift_fst]) (IsPullback.of_hasPullback p t)
  let : IsOpenImmersion i := MorphismProperty.of_isPullback hi inferInstance
  exact isIntegral_of_isOpenImmersion i

end

/-! A surjective open source chart over an open base of a geometrically
integral morphism has geometrically integral fibers. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem geometricallyIntegral_openSquare {E X V U : Scheme.{0}}
    (p : E ⟶ X) [GeometricallyIntegral p] (q : V ⟶ U) [Surjective q]
    (i : U ⟶ X) (j : V ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : q ≫ i = j ≫ p) : GeometricallyIntegral q := by
  let k : V ⟶ pullback p i := pullback.lift j q h.symm
  have hk : k ≫ pullback.fst p i = j := pullback.lift_fst _ _ _
  have hq : k ≫ pullback.snd p i = q := pullback.lift_snd _ _ _
  let : IsOpenImmersion (k ≫ pullback.fst p i) := hk.symm ▸ inferInstance
  let : IsOpenImmersion k := IsOpenImmersion.of_comp k (pullback.fst p i)
  let : Surjective (k ≫ pullback.snd p i) := hq.symm ▸ inferInstance
  have H := geometricallyIntegral_openSource (pullback.snd p i) k
  rwa [hq] at H

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.IntegralOpenSource.BundleCycles
