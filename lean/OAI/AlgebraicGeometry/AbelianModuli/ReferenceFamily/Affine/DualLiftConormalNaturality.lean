import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualDerivationCoefficientMaps

/-! # Dual Lift Conormal Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftConormalNaturality

noncomputable section

/-! A literal coefficient-change square of actual affine lifts gives
the same square in their constructed lift modules and conormal coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k B C C' : Type) [CommRing k] [CommRing B] [CommRing C] [CommRing C']
    [Algebra k B] [Algebra k C] [Algebra k C'] [Algebra B C] [Algebra B C']
    [IsScalarTower k B C] [IsScalarTower k B C'] (q : C →ₐ[B] C')
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = AlgebraAutomorphismNaturality.affineOverAlgHom k B C (IsScalarTower.toAlgHom k B C)})
    (g : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C') ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k C' ≫ f = AlgebraAutomorphismNaturality.affineOverAlgHom k B C' (IsScalarTower.toAlgHom k B C')})
    (h : AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (Dual.NumberCoefficients.dualNumberAlgMap (q.restrictScalars k)) ≫ f.val = g.val)

include h in
theorem affineDualLiftSpaceEquiv_natural :
    DualLiftConormal.affineDualLiftSpaceEquiv k B C' g = Dual.CoefficientLiftNaturality.dualCoefficientLiftMap k B C C' q (DualLiftConormal.affineDualLiftSpaceEquiv k B C f) := by
  apply (DualLiftConormal.affineDualLiftSpaceEquiv k B C').symm.injective
  apply Subtype.ext
  have hf := congrArg (fun z => z.val) ((DualLiftConormal.affineDualLiftSpaceEquiv k B C).symm_apply_apply f)
  have hg := congrArg (fun z => z.val) ((DualLiftConormal.affineDualLiftSpaceEquiv k B C').symm_apply_apply g)
  have hc := DualDerivationCoefficientMaps.affineDualLiftSpaceEquiv_coefficient_map k B C C' q (DualLiftConormal.affineDualLiftSpaceEquiv k B C f)
  rw [hf] at hc
  exact hg.trans (h.symm.trans hc)

variable [Algebra B k] [IsScalarTower k B k] [IsScalarTower B k C] [IsScalarTower B k C']
    [Algebra.FormallySmooth k B]

include h in
theorem affineDualLiftConormalEquiv_natural (z : (RingHom.ker (algebraMap B k)).Cotangent) :
    DualLiftConormal.affineDualLiftConormalEquiv k B C' g z = q (DualLiftConormal.affineDualLiftConormalEquiv k B C f z) := by
  change Dual.AlgebraLiftCoordinates.DualCoefficientLifts.conormalEquiv C' k B (DualLiftConormal.affineDualLiftSpaceEquiv k B C' g) z =
    q (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.conormalEquiv C k B (DualLiftConormal.affineDualLiftSpaceEquiv k B C f) z)
  rw [affineDualLiftSpaceEquiv_natural k B C C' q f g h]
  exact Dual.CoefficientLiftNaturality.dualCoefficientLiftMap_conormal k B C C' q (DualLiftConormal.affineDualLiftSpaceEquiv k B C f) z

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftConormalNaturality
