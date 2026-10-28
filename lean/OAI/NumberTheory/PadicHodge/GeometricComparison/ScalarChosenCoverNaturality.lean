import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRhamScalarCoverInvariance
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineMapRefinement

/-! # Scalar Chosen Cover Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarChosenCoverNaturality.GlobalDeRhamScalarExtension

noncomputable section

/-! Actual global de Rham scalar extension is natural for independently chosen finite affine covers of a quasi-compact source and target. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra ℚ R] [Algebra ℚ S] [Module.Flat R S]
  {X₁ X₂ : Over (Spec (CommRingCat.of R))} [IsSeparated X₁.hom] [IsSeparated X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of S))} [CompactSpace X₁.left]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)
  {ι κ : Type} [Finite ι] [Finite κ] (U : ι → X₂.left.Opens) (V : κ → X₁.left.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (V i))
  (hcoverU : iSup U = ⊤) (hcoverV : iSup V = ⊤)

include hsquare in
theorem chosen_cover_naturality (n : ℕ) (x : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X₂ n) :
    GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension.equiv R X₁ V hV hcoverV S Y₁ f₁ hp₁ n ((DeRham.Int.pullback u n).baseChange S x) =
      DeRham.Int.pullback v n (GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension.equiv R X₂ U hU hcoverU S Y₂ f₂ hp₂ n x) := by
  let W := GeometricComparison.Finite.AffineMapRefinement.FiniteAffineMapRefinement.ofCompact u.left U V hcoverU hcoverV
  let : Fintype W.Index := W.finite
  have hmap := GlobalDeRhamScalarNaturality.GlobalDeRhamScalarExtension.naturality R S u v f₁ f₂ hp₁ hp₂ hsquare U W.opens
    (fun i => (W.index i).1) (GeometricComparison.Finite.AffineMapRefinement.FiniteAffineMapRefinement.le_source u.left U V hcoverU hcoverV)
    hU W.affine hcoverU W.cover n x
  have href := DeRhamScalarCoverInvariance.GlobalDeRhamScalarExtension.refinement_invariance R S X₁ Y₁ f₁ hp₁ V W.opens
    (fun i => (W.index i).2) (GeometricComparison.Finite.AffineMapRefinement.FiniteAffineMapRefinement.le_target u.left U V hcoverU hcoverV)
    hV W.affine hcoverV W.cover n ((DeRham.Int.pullback u n).baseChange S x)
  exact href.symm.trans hmap

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarChosenCoverNaturality.GlobalDeRhamScalarExtension
