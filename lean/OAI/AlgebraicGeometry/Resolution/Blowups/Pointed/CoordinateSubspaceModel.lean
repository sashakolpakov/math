import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterPointedFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedEtaleFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceIdeal

/-! # Coordinate Subspace Model -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.CoordinateSubspaceModel.Construction

noncomputable section

/-! Every point of a smooth closed center has an actual open ambient chart mapping étale to a standard coordinate-subspace model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

theorem exists_pointed_coordinate_subspace_open_model
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (I : Ideal R) [Algebra.Smooth k (R ⧸ I)]
    (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
      ∃ q : PrimeSpectrum S, PrimeSpectrum.comap f.toRingHom q = p ∧
      ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (n : ℕ)
        (φ : MvPolynomial (ι ⊕ Fin n) k →ₐ[k] S), φ.toRingHom.Etale ∧
        I.map f.toRingHom = (RingHom.ker Coordinate.SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom).map φ.toRingHom := by
  classical
  obtain ⟨A, hAk, hAs, fA, hfA, qA, hqA, ι, hι, hdec, v, D, hD, hI⟩ :=
    Blowups.Smooth.CenterPointedFrame.Construction.smooth_center_pointed_open_frame (k := k) I p hp
  let : Algebra k A := hAk
  let : Algebra.Smooth k A := hAs
  let : Fintype ι := hι
  let : DecidableEq ι := hdec
  let : qA.asIdeal.IsPrime := qA.isPrime
  obtain ⟨r, hr, n, ψ, hψ, hψk, hψv⟩ := AdaptedEtaleFrame.Construction.exists_adapted_etale_frame D v hD qA.asIdeal
  let S := Localization.Away r
  let : Algebra.Smooth A S := Algebra.Smooth.of_isLocalization_Away r
  let : Algebra.Smooth k S := Algebra.Smooth.comp k A S
  let fS : A →ₐ[k] S := IsScalarTower.toAlgHom k A S
  let f := fS.comp fA
  let e := MvPolynomial.renameEquiv k (Equiv.sumComm ι (Fin n))
  let ρ := ψ.comp e.toRingHom
  have hρk (c : k) : ρ (C c) = algebraMap k S c := by
    change ψ (MvPolynomial.rename (Equiv.sumComm ι (Fin n)) (C c)) = _
    rw [MvPolynomial.rename_C]
    exact hψk c
  let φ : MvPolynomial (ι ⊕ Fin n) k →ₐ[k] S :=
    { __ := ρ
      commutes' := hρk }
  have hφ : φ.toRingHom.Etale := RingHom.Etale.stableUnderComposition e.toRingHom ψ
    (RingHom.Etale.of_bijective e.bijective) hψ
  have hφv (i : ι) : φ (X (Sum.inl i)) = algebraMap A S (v i) := by
    change ψ (MvPolynomial.rename (Equiv.sumComm ι (Fin n)) (X (Sum.inl i))) = _
    rw [MvPolynomial.rename_X]
    exact hψv i
  obtain ⟨q, hq⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime r qA hr
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom fA.toRingHom)) := hfA
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom fS.toRingHom)) := IsOpenImmersion.of_isLocalization r
  have hf : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom fA.toRingHom ≫ CommRingCat.ofHom fS.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  refine ⟨.of S, inferInstance, inferInstance, f, hf, q, ?_, ι, hι, hdec, n, φ, hφ, ?_⟩
  · apply PrimeSpectrum.ext
    change (q.asIdeal.comap fS.toRingHom).comap fA.toRingHom = p.asIdeal
    have he : q.asIdeal.comap fS.toRingHom = qA.asIdeal := congrArg PrimeSpectrum.asIdeal hq
    rw [he]
    exact congrArg PrimeSpectrum.asIdeal hqA
  · change I.map (fS.toRingHom.comp fA.toRingHom) = _
    rw [← Ideal.map_map, hI, Coordinate.SubspaceIdeal.Construction.polynomialCoordinateProjection_ker_eq_span, Ideal.map_span, Ideal.map_span]
    congr 1
    rw [← Set.range_comp, ← Set.range_comp]
    congr 1
    funext i
    exact (hφv i).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.CoordinateSubspaceModel.Construction
