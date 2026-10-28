import OAI.NumberTheory.PadicHodge.GeometricComparison.GlobalDeRhamScalarNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Functor

/-! # De Rham Scalar Cover Invariance -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRhamScalarCoverInvariance.GlobalDeRhamScalarExtension

noncomputable section

/-! The original global scalar equivalence is unchanged under an actual affine refinement of its chosen cover. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra ℚ R] [Algebra ℚ S] [Module.Flat R S]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  (Y : Over (Spec (CommRingCat.of S))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  {ι κ : Type} [Finite ι] [Finite κ] (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ U (r i))
  (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (V i))
  (hcoverU : iSup U = ⊤) (hcoverV : iSup V = ⊤)

include hr in
theorem refinement_invariance (n : ℕ) (x : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X n) :
    GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension.equiv R X V hV hcoverV S Y f hp n x = GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension.equiv R X U hU hcoverU S Y f hp n x := by
  have hs : f ≫ 𝟙 X.left = 𝟙 Y.left ≫ f := (Category.comp_id f).trans (Category.id_comp f).symm
  have h := GlobalDeRhamScalarNaturality.GlobalDeRhamScalarExtension.naturality R S (𝟙 X) (𝟙 Y) f f hp hp hs U V r hr hU hV hcoverU hcoverV n x
  simpa only [DeRham.Functor.pullback_id, LinearMap.baseChange_id, LinearMap.id_apply] using h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRhamScalarCoverInvariance.GlobalDeRhamScalarExtension
