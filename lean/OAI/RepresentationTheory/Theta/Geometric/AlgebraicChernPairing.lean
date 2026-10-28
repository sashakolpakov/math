import OAI.RepresentationTheory.Theta.Geometric.ContinuousGroupPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernClassOperations
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MultiplicationPeriods

/-! # Algebraic Chern Pairing -/

namespace OAI.RepresentationTheory.Theta.Geometric.AlgebraicChernPairing

noncomputable section

/-! The original native Chern form is functorial for actual algebraic
group maps; multiplication by an integer scales it by the integer squared. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernClassOperations OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MultiplicationPeriods.IntrinsicLinearMaps

variable {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}

theorem nativeChernForm_algebraic_pullback (f : A.toOver ⟶ B.toOver) [IsMonHom f]
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.toOver.left) (v w : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A (L.pullback f.left) v w = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm B L (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f v) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f w) := by
  let F := TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)
  have hs : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeMultiplication A ≫ F =
      AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((F, F) : (AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver, AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver) ⟶
        (AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver, AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver)) ≫ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeMultiplication B := by
    apply TopCat.ext
    intro p
    exact MonObj.mul_comp p.1 p.2 f
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing.alternatingClassPairing _ _ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation (L.pullback f.left))
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A w) = _
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernEmbeddingIndependence.lineBundleChernClass_pullback f L]
  have h := ContinuousGroupPairing.alternatingClassPairing_continuous_naturality
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeMultiplication A) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeMultiplication B) F hs
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass B.variety.presentation L) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A w)
  exact h.trans (congrArg₂
    (fun x y => AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing.alternatingClassPairing (AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeMultiplication B)
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass B.variety.presentation L) x y)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality f v).symm (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality f w).symm)

theorem nativeChernForm_multiplication (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (v w : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A (L.pullback ((𝟙 A.toOver) ^ n).left) v w =
      (n : ℚ) ^ 2 * AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L v w := by
  rw [nativeChernForm_algebraic_pullback, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MultiplicationPeriods.IntrinsicLinearMaps.rationalLift_multiplication]
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L (n • v) (n • w) = _
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  ring

end

end OAI.RepresentationTheory.Theta.Geometric.AlgebraicChernPairing
