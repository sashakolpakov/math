import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPullbackScalarExtension
import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarChosenCoverNaturality

/-! # Quasi Compact Scalar Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.QuasiCompactScalarNaturality.QuasiCompactFilteredBaseChange

noncomputable section

/-! The constructed filtered comparison for quasi-compact separated schemes is natural in the original geometric de Rham pullback. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra ℚ R] [Algebra ℚ S] [Module.Flat R S]
  {X₁ X₂ : Over (Spec (CommRingCat.of R))}
  [QuasiCompact X₁.hom] [QuasiCompact X₂.hom] [IsSeparated X₁.hom] [IsSeparated X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of S))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)

include hsquare in
theorem naturality (n : ℕ) (x : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X₂ n) :
    IntrinsicPullbackScalarExtension.QuasiCompactFilteredBaseChange.equiv R S X₁ Y₁ f₁ hp₁ n ((DeRham.Int.pullback u n).baseChange S x) =
      DeRham.Int.pullback v n (IntrinsicPullbackScalarExtension.QuasiCompactFilteredBaseChange.equiv R S X₂ Y₂ f₂ hp₂ n x) := by
  let : CompactSpace X₁.left := QuasiCompact.compactSpace_of_compactSpace X₁.hom
  exact ScalarChosenCoverNaturality.GlobalDeRhamScalarExtension.chosen_cover_naturality R S u v f₁ f₂ hp₁ hp₂ hsquare
    (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens R X₂) (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens R X₁)
    (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_affine R X₂) (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_affine R X₁)
    (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_cover R X₂) (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_cover R X₁) n x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.QuasiCompactScalarNaturality.QuasiCompactFilteredBaseChange
