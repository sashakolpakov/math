import OAI.RepresentationTheory.Theta.Geometric.RealPeriodHomology
import OAI.RepresentationTheory.Theta.Geometric.ContinuousGroupPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing

/-! # Real Chern Pairing -/

namespace OAI.RepresentationTheory.Theta.Geometric.RealChernPairing

noncomputable section

/-! Original native Chern forms transport under an actual continuous
group map and its real period lift, whenever its Chern classes transport. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped _root_.CategoryTheory.MonObj

namespace RealPeriodMaps
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing

local instance realChernPairing_integral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property

variable {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (T : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
    (hT : ∀ v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A, T v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B)
    (f : AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver ⟶ AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver)
    (hf : ∀ v : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A,
      f (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input A (QuotientAddGroup.mk v)) =
        AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input B (QuotientAddGroup.mk (T v)))
    (hm : ∀ x y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver, f (x * y) =
      (show AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver from f x) * (show AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver from f y))

include hf hm in
theorem nativeChernForm_continuous_naturality
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (M : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.toOver.left)
    (hc : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 2
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass B.variety.presentation M))
    (v w : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L v w = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm B M (RealPeriodCoe.RealPeriodMaps.rationalMap T hT v) (RealPeriodCoe.RealPeriodMaps.rationalMap T hT w) := by
  have hs : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeMultiplication A ≫ f =
      AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, f) : (AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver, AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver) ⟶
        (AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver, AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver)) ≫ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeMultiplication B := by
    apply TopCat.ext
    intro p
    exact hm p.1 p.2
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing.alternatingClassPairing _ _ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A w) = _
  rw [hc, ContinuousGroupPairing.alternatingClassPairing_continuous_naturality
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeMultiplication A) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeMultiplication B) f hs,
    ← RealPeriodHomology.RealPeriodMaps.nativeHomology_naturality T hT f hf, ← RealPeriodHomology.RealPeriodMaps.nativeHomology_naturality T hT f hf]
  rfl

end RealPeriodMaps

end

end OAI.RepresentationTheory.Theta.Geometric.RealChernPairing
