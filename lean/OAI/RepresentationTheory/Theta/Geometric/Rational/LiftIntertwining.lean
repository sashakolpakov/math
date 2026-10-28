import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps

/-! # Lift Intertwining -/

namespace OAI.RepresentationTheory.Theta.Geometric.Rational.LiftIntertwining

noncomputable section

/-! Original commuting scheme maps induce the same commuting square
on their actual native rational period spaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps

theorem rationalLift_intertwining_apply {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) (a : A.toOver ⟶ A.toOver) (b : B.toOver ⟶ B.toOver)
    [IsMonHom f] [IsMonHom a] [IsMonHom b] (h : a ≫ f = f ≫ b) (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift a v) = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift b (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f v) :=
  LinearMap.congr_fun ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp a f).symm.trans
    ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_congr _ _ h).trans (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp f b))) v

end

end OAI.RepresentationTheory.Theta.Geometric.Rational.LiftIntertwining
