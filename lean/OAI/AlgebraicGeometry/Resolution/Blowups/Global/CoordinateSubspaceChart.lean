import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceTranslationMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceIdeal

/-! # Coordinate Subspace Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.CoordinateSubspaceChart.Construction

noncomputable section

/-! Pointed actual affine charts identify a closed ideal with a standard coordinate-subspace ideal under an étale map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure GlobalCoordinateSubspaceChart {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (J : X.IdealSheafData) (x : X) where
  ring : CommRingCat
  algebra : Algebra ℂ ring
  smooth : Algebra.Smooth ℂ ring
  domain : IsDomain ring
  map : Spec ring ⟶ X
  isOpenImmersion : IsOpenImmersion map
  ground : map ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure ring
  point : PrimeSpectrum ring
  point_over : map point = x
  normal : Type
  normalFinite : Fintype normal
  normalDecidableEq : DecidableEq normal
  freeDimension : ℕ
  coordinate : MvPolynomial (normal ⊕ Fin freeDimension) ℂ →ₐ[ℂ] ring
  coordinate_etale : coordinate.toRingHom.Etale
  modelNonzero : RingHom.ker (Coordinate.SubspaceIdeal.Construction.polynomialCoordinateProjection (σ := normal) (τ := Fin freeDimension) (R := ℂ)).toRingHom ≠ ⊥
  ideal_eq : J.comap map = Affine.QuotientKernel.Construction.affineQuotientKernel
    ((RingHom.ker Coordinate.SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom).map coordinate.toRingHom)

attribute [instance] GlobalCoordinateSubspaceChart.algebra GlobalCoordinateSubspaceChart.smooth
  GlobalCoordinateSubspaceChart.domain GlobalCoordinateSubspaceChart.isOpenImmersion
  GlobalCoordinateSubspaceChart.normalFinite GlobalCoordinateSubspaceChart.normalDecidableEq

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.CoordinateSubspaceChart.Construction
