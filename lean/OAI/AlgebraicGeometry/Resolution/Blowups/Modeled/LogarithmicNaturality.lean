import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicCoordinateBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.LogarithmicCoordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations
import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicFiltration

/-! # Logarithmic Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Logarithmic ideals agree on common étale refinements of actual boundary models. -/

universe u v

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.iterated_logarithmic_map
    {k R S : Type u} {ι : Type v} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] {w : ι → R} (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (φ : R →ₐ[k] S) (hφ : φ.toRingHom.Etale) (J : Ideal R) (n : ℕ) :
    (Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n).map φ.toRingHom =
      Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k (fun j => φ (w j)) (J.map φ.toRingHom) n := by
  let : Algebra R S := φ.toRingHom.toAlgebra
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
  let : Algebra.Etale R S := RingHom.etale_algebraMap.mp hφ
  let P := MvPolynomial M.indices k
  let : Algebra P R := M.map.toAlgebra
  let : Algebra.Etale P R := RingHom.etale_algebraMap.mp M.etale
  let : IsScalarTower k P R := IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  let : Algebra P S := (φ.toRingHom.comp M.map).toAlgebra
  let : IsScalarTower P R S := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.Etale P S := Algebra.Etale.comp P R S
  let : IsScalarTower k P S := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap k S c = φ (M.map (MvPolynomial.C c))
    rw [M.ground, φ.commutes])
  rw [M.iterated_logarithmic_coordinates, (M.baseChange φ hφ).iterated_logarithmic_coordinates]
  exact LogarithmicCoordinateBaseChange.Construction.iteratedRelativeLogarithmicDifferentialIdeal_coordinate_baseChange M.boundaryIndices J n

theorem Modeled.LogarithmicNaturality.Construction.logarithmic_ideals_agree_on_common_etale_refinement
    {k R S T : Type u} {ι : Type v} [Field k] [CommRing R] [CommRing S] [CommRing T]
    [Algebra k R] [Algebra k S] [Algebra k T]
    (φ : R →ₐ[k] T) (ψ : S →ₐ[k] T) (hφ : φ.toRingHom.Etale) (hψ : ψ.toRingHom.Etale)
    (w : ι → R) (v : ι → S) (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (N : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k S ι v)
    (hboundary : ∀ j, (Ideal.span {w j}).map φ.toRingHom = (Ideal.span {v j}).map ψ.toRingHom)
    (J : Ideal R) (K : Ideal S) (hJK : J.map φ.toRingHom = K.map ψ.toRingHom) (n : ℕ) :
    (Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n).map φ.toRingHom =
      (Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k v K n).map ψ.toRingHom := by
  rw [M.iterated_logarithmic_map φ hφ, N.iterated_logarithmic_map ψ hψ, hJK]
  apply LogarithmicFiltration.Construction.iteratedRelativeLogarithmicDifferentialIdeal_eq_of_principal_ideals (k := k)
    (fun j => φ (w j)) (fun j => ψ (v j))
  intro j
  have h := hboundary j
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton] at h
  exact h

end

end OAI.AlgebraicGeometry.Resolution.Blowups
