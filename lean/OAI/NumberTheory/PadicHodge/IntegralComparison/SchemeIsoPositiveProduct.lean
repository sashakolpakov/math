import OAI.NumberTheory.PadicHodge.IntegralComparison.Rational.CoverScalarIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ScalarPositiveProduct

/-! # Scheme Iso Positive Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeIsoPositiveProduct

noncomputable section

/-! A genuine scheme isomorphism carries nonzero ordinary Čech cup
products to the inverse-image affine cover over the same field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type) [Field R] [Algebra ℚ R]
  (X Y : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom] (e : Y ≅ X)

local instance schemeMap_isIso : IsIso e.hom.left := (Over.forget _).map_isIso e.hom

omit [Algebra ℚ R] [IsSeparated X.hom] in
theorem square : IsPullback e.hom.left Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap R R))) := by
  have hid : Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 (Spec (CommRingCat.of R)) := by
    change Spec.map (𝟙 (CommRingCat.of R)) = _
    exact Spec.map_id _
  rw [hid]
  exact IsPullback.of_horiz_isIso ⟨e.hom.w.trans (Category.comp_id _).symm⟩

variable {ι : Type} [Finite ι] (U : ι → X.left.Opens)
  (hU : iSup U = ⊤) (haU : ∀ i, IsAffineOpen (U i))

def inverseCover : ι → Y.left.Opens := fun i => e.hom.left ⁻¹ᵁ U i

include hU in
omit [Algebra ℚ R] [IsSeparated X.hom] [Finite ι] in
theorem cover : iSup (inverseCover R X Y e U) = ⊤ := by
  change iSup (fun i => e.hom.left ⁻¹ᵁ U i) = ⊤
  rw [← Scheme.Hom.preimage_iSup, hU]
  rfl

include haU in
omit [Algebra ℚ R] [IsSeparated X.hom] [Finite ι] in
theorem affine (i : ι) : IsAffineOpen (inverseCover R X Y e U i) :=
  (haU i).preimage_of_isIso e.hom.left

include haU in
theorem exists_nonzero (n : ℕ)
    (hn : ∃ v : Fin (n+1) → (IntegralDeRham.CechProduct.total R X
        (NonemptyCechNerve.nerve U)).homology 1,
      GradedPositiveProduct.product (fun i j x y =>
        IntegralDeRham.CechProduct.cohomologyCup R X (NonemptyCechNerve.nerve U) i j x y) n v ≠ 0) :
    ∃ v : Fin (n+1) → (IntegralDeRham.CechProduct.total R Y
        (NonemptyCechNerve.nerve (inverseCover R X Y e U))).homology 1,
      GradedPositiveProduct.product (fun i j x y =>
        IntegralDeRham.CechProduct.cohomologyCup R Y
          (NonemptyCechNerve.nerve (inverseCover R X Y e U)) i j x y) n v ≠ 0 := by
  let : IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap R R X Y e.hom.left
      (square R X Y e).w U (n+1)) :=
    Rational.CoverScalarIso.homologyMap_isIso R R X Y e.hom.left (square R X Y e) U haU (n+1)
  exact Intrinsic.ScalarPositiveProduct.target_exists_nonzero R R X Y e.hom.left
    (square R X Y e).w U n hn

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeIsoPositiveProduct
