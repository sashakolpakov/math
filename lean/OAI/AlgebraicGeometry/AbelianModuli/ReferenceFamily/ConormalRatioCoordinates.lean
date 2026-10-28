import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormal

/-! # Conormal Ratio Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConormalRatioCoordinates

noncomputable section

/-! Conormal coordinates of an actual group lift depend only on
its quotient by the reference lift. This applies over arbitrary
coefficient algebras and retains the original affine identity chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k B C : Type) [CommRing k] [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] [Algebra B C] [IsScalarTower k B C]
    [Algebra B k] [IsScalarTower k B k] [IsScalarTower B k C]
    {A : Over (Spec (.of k))} [GrpObj A]
    (i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A) [IsOpenImmersion i.left]
    (hi : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B k (IsScalarTower.toAlgHom k B k) ≫ i = 1)
    [Algebra.FormallySmooth k B]

theorem groupCoefficientConormalEquiv_eq_of_ratio
    (c c' : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A)
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c})
    (g : {g : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ g = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ c'})
    (h : f.val / c = g.val / c') :
    GroupCoefficientConormal.groupCoefficientConormalEquiv k B C i hi c f = GroupCoefficientConormal.groupCoefficientConormalEquiv k B C i hi c' g := by
  apply congrArg (Affine.DualLiftConormal.affineDualLiftConormalEquiv k B C)
  apply Subtype.ext
  have : Mono i := Over.mono_of_mono_left i
  apply (cancel_mono i).mp
  have hf := eq_div_of_mul_eq' (GroupCoefficientConormal.groupCoefficientOpenLift_recovery k B C i hi c f)
  have hg := eq_div_of_mul_eq' (GroupCoefficientConormal.groupCoefficientOpenLift_recovery k B C i hi c' g)
  exact hf.trans (h.trans hg.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConormalRatioCoordinates
