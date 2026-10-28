import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.AffineOrderApproximation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.FiniteAffine

/-! # Common Affine Order Approximation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.CommonAffineOrderApproximation.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual finite-point order approximation on schemes affine over projective schemes -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem exists_commonAffine_prescribed_orders {ι : Type*} [Finite ι]
    (x : ι → X) (hx : ∀ i, coheight (x i) = 1) (hinj : Function.Injective x)
    [∀ i, IsIntegrallyClosed (X.presheaf.stalk (x i))]
    (U : X.Opens) (hU : IsAffineOpen U) (hxU : ∀ i, x i ∈ U) (n : ι → ℤ) :
    ∃ g : X.functionFieldˣ, ∀ i, X.ord (g : X.functionField) (x i) = n i := by
  classical
  by_cases hι : Nonempty ι
  · let := hι
    let : Nonempty U := ⟨⟨x (Classical.choice hι), hxU _⟩⟩
    let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hpre : ∀ i, ∃ y : Spec Γ(X, U), hU.fromSpec y = x i := by
      intro i
      exact (show x i ∈ Set.range hU.fromSpec by rw [IsAffineOpen.range_fromSpec]; exact hxU i)
    choose y hy using hpre
    have hyh : ∀ i, coheight (hU.fromSpec (y i)) = 1 := fun i => by rw [hy i]; exact hx i
    have hyinj : Function.Injective y := by
      intro i j hij
      apply hinj
      exact (hy i).symm.trans ((congrArg hU.fromSpec hij).trans (hy j))
    let : ∀ i, IsIntegrallyClosed (X.presheaf.stalk (hU.fromSpec (y i))) :=
      fun i => (hy i).symm ▸ inferInstance
    obtain ⟨g, hg⟩ := Open.AffineOrderApproximation.BundleCycles.exists_openAffine_prescribed_orders hU.fromSpec y hyh hyinj n
    exact ⟨g, fun i => (hy i) ▸ hg i⟩
  · let : IsEmpty ι := not_nonempty_iff.mp hι
    exact ⟨1, fun i => isEmptyElim i⟩

theorem exists_affineOverProjective_prescribed_orders {Y : Scheme.{0}} {f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Y f) (q : X ⟶ Y) [IsAffineHom q]
    {ι : Type*} [Finite ι] (x : ι → X) (hx : ∀ i, coheight (x i) = 1)
    (hinj : Function.Injective x) [∀ i, IsIntegrallyClosed (X.presheaf.stalk (x i))]
    (n : ι → ℤ) : ∃ g : X.functionFieldˣ, ∀ i, X.ord (g : X.functionField) (x i) = n i := by
  obtain ⟨U, hU, hxU⟩ := Projective.FiniteAffine.BundleCycles.exists_affineOverProjective_commonAffine P q x
  exact exists_commonAffine_prescribed_orders x hx hinj U hU hxU n

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.CommonAffineOrderApproximation.BundleCycles
