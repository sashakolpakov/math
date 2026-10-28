import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.GlobalOneNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Functor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineMapRefinement

/-! # Chosen Cover Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ChosenCoverNaturality.IntegralGlobalHOneBaseChange

noncomputable section

/-! The existing integral H-one scalar comparison is independent of affine
refinements and natural for independently chosen finite affine covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  [Module.Flat ℤ R] [Module.Flat ℤ S] [Module.Flat R S]

section Refinement
variable (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  (Y : Over (Spec (CommRingCat.of S))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  {ι κ : Type} [Finite ι] [Finite κ] (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ U (r i))
  (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (V i))
  (hcoverU : iSup U = ⊤) (hcoverV : iSup V = ⊤)

include hr in
theorem refinement_invariance (x : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X 1) :
    GlobalOneBaseChange.IntegralGlobalHOneBaseChange.equiv R X V hV hcoverV S Y f hp x = GlobalOneBaseChange.IntegralGlobalHOneBaseChange.equiv R X U hU hcoverU S Y f hp x := by
  have hs : f ≫ 𝟙 X.left = 𝟙 Y.left ≫ f := (Category.comp_id f).trans (Category.id_comp f).symm
  have h := GlobalOneNaturality.IntegralGlobalHOneBaseChange.naturality R S (𝟙 X) (𝟙 Y) f f hp hp hs U V r hr hU hV hcoverU hcoverV x
  simpa only [DeRham.Functor.pullback_id, LinearMap.baseChange_id, LinearMap.id_apply] using h
end Refinement

variable {X₁ X₂ : Over (Spec (CommRingCat.of R))} [IsSeparated X₁.hom] [IsSeparated X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of S))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)

include hsquare in
theorem chosen_cover_naturality [CompactSpace X₁.left]
    {ι κ : Type} [Finite ι] [Finite κ] (U : ι → X₂.left.Opens) (V : κ → X₁.left.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (V i))
    (hcoverU : iSup U = ⊤) (hcoverV : iSup V = ⊤)
    (x : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X₂ 1) :
    GlobalOneBaseChange.IntegralGlobalHOneBaseChange.equiv R X₁ V hV hcoverV S Y₁ f₁ hp₁ ((DeRham.Int.pullback u 1).baseChange S x) =
      DeRham.Int.pullback v 1 (GlobalOneBaseChange.IntegralGlobalHOneBaseChange.equiv R X₂ U hU hcoverU S Y₂ f₂ hp₂ x) := by
  let W := GeometricComparison.Finite.AffineMapRefinement.FiniteAffineMapRefinement.ofCompact u.left U V hcoverU hcoverV
  let : Fintype W.Index := W.finite
  have hmap := GlobalOneNaturality.IntegralGlobalHOneBaseChange.naturality R S u v f₁ f₂ hp₁ hp₂ hsquare U W.opens
    (fun i => (W.index i).1) (GeometricComparison.Finite.AffineMapRefinement.FiniteAffineMapRefinement.le_source u.left U V hcoverU hcoverV)
    hU W.affine hcoverU W.cover x
  have href := refinement_invariance R S X₁ Y₁ f₁ hp₁ V W.opens
    (fun i => (W.index i).2) (GeometricComparison.Finite.AffineMapRefinement.FiniteAffineMapRefinement.le_target u.left U V hcoverU hcoverV)
    hV W.affine hcoverV W.cover ((DeRham.Int.pullback u 1).baseChange S x)
  exact href.symm.trans hmap

include hsquare in
theorem quasiCompactEquiv_naturality [QuasiCompact X₁.hom] [QuasiCompact X₂.hom]
    (x : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X₂ 1) :
    GlobalOneBaseChange.IntegralGlobalHOneBaseChange.quasiCompactEquiv R X₁ S Y₁ f₁ hp₁ ((DeRham.Int.pullback u 1).baseChange S x) =
      DeRham.Int.pullback v 1 (GlobalOneBaseChange.IntegralGlobalHOneBaseChange.quasiCompactEquiv R X₂ S Y₂ f₂ hp₂ x) := by
  let : CompactSpace X₁.left := QuasiCompact.compactSpace_of_compactSpace X₁.hom
  exact chosen_cover_naturality R S u v f₁ f₂ hp₁ hp₂ hsquare
    (GeometricComparison.Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens R X₂) (GeometricComparison.Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens R X₁)
    (GeometricComparison.Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_affine R X₂) (GeometricComparison.Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_affine R X₁)
    (GeometricComparison.Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_cover R X₂) (GeometricComparison.Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_cover R X₁) x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ChosenCoverNaturality.IntegralGlobalHOneBaseChange
