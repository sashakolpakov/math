import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel

/-! # Smooth -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Smoothness supplied by the actual étale coordinate map in a boundary model. -/

universe u v

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.smooth {k R : Type u} {ι : Type v}
    [CommRing k] [CommRing R] [Algebra k R] {w : ι → R}
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) : Algebra.Smooth k R := by
  let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
  let : Algebra.Etale (MvPolynomial M.indices k) R := RingHom.etale_algebraMap.mp M.etale
  let : IsScalarTower k (MvPolynomial M.indices k) R :=
    IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  let : Algebra.Smooth k (MvPolynomial M.indices k) := ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.comp k (MvPolynomial M.indices k) R

end

end OAI.AlgebraicGeometry.Resolution.Blowups
