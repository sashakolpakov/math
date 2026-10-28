import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPullbackScalarExtension
import OAI.NumberTheory.PadicHodge.GeometricComparison.QuasiCompactScalarNaturality

/-! # Pullback Scalar Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.PullbackScalarNaturality.IntrinsicPullbackScalarExtension

noncomputable section

/-! Naturality of filtered scalar extension on the canonical geometric pullback objects. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra ℚ R] [Algebra ℚ S] [Module.Flat R S]
  {X₁ X₂ : Over (Spec (CommRingCat.of R))}
  [QuasiCompact X₁.hom] [QuasiCompact X₂.hom] [IsSeparated X₁.hom] [IsSeparated X₂.hom]
  (u : X₁ ⟶ X₂)

theorem naturality (n : ℕ) (x : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X₂ n) :
    IntrinsicPullbackScalarExtension.equiv R S X₁ n ((DeRham.Int.pullback u n).baseChange S x) =
      DeRham.Int.pullback ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map u) n
        (IntrinsicPullbackScalarExtension.equiv R S X₂ n x) := by
  let base := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let Y₁ : Over (Spec (CommRingCat.of S)) := (Over.pullback base).obj X₁
  let Y₂ : Over (Spec (CommRingCat.of S)) := (Over.pullback base).obj X₂
  let v : Y₁ ⟶ Y₂ := (Over.pullback base).map u
  let f₁ : Y₁.left ⟶ X₁.left := pullback.fst X₁.hom base
  let f₂ : Y₂.left ⟶ X₂.left := pullback.fst X₂.hom base
  have hp₁ : IsPullback f₁ Y₁.hom X₁.hom base := IsPullback.of_hasPullback X₁.hom base
  have hp₂ : IsPullback f₂ Y₂.hom X₂.hom base := IsPullback.of_hasPullback X₂.hom base
  have hs : f₁ ≫ u.left = v.left ≫ f₂ := (pullback.lift_fst _ _ _).symm
  exact QuasiCompactScalarNaturality.QuasiCompactFilteredBaseChange.naturality R S u v f₁ f₂ hp₁ hp₂ hs n x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.PullbackScalarNaturality.IntrinsicPullbackScalarExtension
