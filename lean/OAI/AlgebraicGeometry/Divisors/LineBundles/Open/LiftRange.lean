import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Lift Range -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.LiftRange.BundleCycles

noncomputable section

/-! # LineBundleCycles: ranges of actual lifts through open immersions -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem range_openLift {A U X : Scheme.{0}} (i : U ⟶ X) [IsOpenImmersion i]
    (g : A ⟶ X) (l : A ⟶ U) (hl : l ≫ i = g) : Set.range l = i ⁻¹' Set.range g := by
  ext u
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, (congrArg (fun f : A ⟶ X => f a) hl).symm⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, i.isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun f : A ⟶ X => f a) hl).trans ha

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.LiftRange.BundleCycles
