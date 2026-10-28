import OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientFrameBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedEtaleFrame

/-! # Normal Quotient Open Frame -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientOpenFrame.Construction

noncomputable section

/-! Lift exact quotient coordinates to actual ambient opens, retaining the normal equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem quotient_dual_frame_lifts_to_pointed_open
    {k R Q ι : Type u} [CommRing k] [CommRing R] [CommRing Q]
    [Algebra k R] [Algebra k Q] [Algebra.Smooth k R]
    [Fintype ι] [DecidableEq ι]
    (q : R →ₐ[k] Q) (hq : Function.Surjective q)
    (z : R) (hqz : q z = 0) (D : Derivation k R R) (hDz : D z = 1)
    (g : ι → R) (δ : ι → Derivation k Q Q)
    (hδ : ∀ i j, δ i (q (g j)) = if i = j then 1 else 0)
    (p : PrimeSpectrum R) (hqp : RingHom.ker q.toRingHom ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
      ∃ (P : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom P = p ∧
      ∃ E : Option ι → Derivation k S S,
        ∀ i j, E i (f (AdaptedEtaleFrame.Construction.transverseExtendedCoordinates g z j)) = if i = j then 1 else 0 := by
  classical
  choose E hEz hE using fun i =>
    Blowups.Smooth.ConormalDerivationLift.Construction.exists_quotient_derivation_lift_annihilating_normal k q hq (δ i) z hqz D hDz
  let a := (JacobianDerivationFrame.Construction.derivationJacobian E g).det
  have hqa : q a = 1 := by
    have hm : q.toRingHom.mapMatrix (JacobianDerivationFrame.Construction.derivationJacobian E g) = 1 := by
      ext i j
      change q (E i (g j)) = (1 : Matrix ι ι Q) i j
      rw [hE, Matrix.one_apply]
      exact hδ i j
    change q.toRingHom (JacobianDerivationFrame.Construction.derivationJacobian E g).det = 1
    rw [RingHom.map_det, hm, Matrix.det_one]
  have ha : a ∉ p.asIdeal := by
    have hm : a - 1 ∈ p.asIdeal := hqp (by
      change q (a - 1) = 0
      rw [map_sub, hqa, map_one, sub_self])
    intro ha
    exact p.isPrime.one_notMem (by
      simpa only [sub_sub_cancel] using p.asIdeal.sub_mem ha hm)
  let S := JacobianNeighborhood.Construction.derivationJacobianNeighborhood E g
  let : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away a
  let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
  let : Algebra.Etale R S := Algebra.Etale.of_isLocalizationAway a
  let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  obtain ⟨P, hP⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime a p ha
  let g' : ι → S := fun i => f (g i)
  let E' := JacobianDerivationFrame.Construction.normalizedJacobianFrame (JacobianNeighborhood.Construction.jacobianNeighborhoodDerivation E g) g'
  have hE'g : ∀ i j, E' i (g' j) = if i = j then 1 else 0 :=
    JacobianDerivationFrame.Construction.normalizedJacobianFrame_dual _ _ (JacobianNeighborhood.Construction.jacobianNeighborhood_jacobian_isUnit E g)
  have hE'z : ∀ i, E' i (f z) = 0 := by
    apply TransverseFiniteFrameCorrection.Construction.normalizedJacobianFrame_annihilates
    intro i
    change JacobianNeighborhood.Construction.jacobianNeighborhoodDerivation E g i (algebraMap R S z) = 0
    rw [JacobianNeighborhood.Construction.jacobianNeighborhoodDerivation_constants, hEz, map_zero]
  let D' := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D
  have hD'z : D' (f z) = 1 := by
    change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D (algebraMap R S z) = 1
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hDz, map_one]
  obtain ⟨F, hFz, hFg⟩ :=
    TransverseFiniteFrameCorrection.Construction.exists_normal_derivation_annihilating_frame D' E' g' (f z) hD'z hE'z hE'g
  refine ⟨.of S, inferInstance, inferInstance, f, IsOpenImmersion.of_isLocalization a,
    P, hP, AdaptedEtaleFrame.Construction.transverseExtendedDerivations E' F (f z), ?_⟩
  have he : (fun j => f (AdaptedEtaleFrame.Construction.transverseExtendedCoordinates g z j)) =
      AdaptedEtaleFrame.Construction.transverseExtendedCoordinates g' (f z) := by
    funext j
    cases j <;> rfl
  intro i j
  rw [congrFun he j]
  exact AdaptedEtaleFrame.Construction.transverseExtendedDerivations_dual E' g' F (f z) hE'g hFz hFg i j

theorem quotient_dual_frame_lifts_to_pointed_coordinates
    {k R Q ι : Type u} [CommRing k] [CommRing R] [CommRing Q]
    [Algebra k R] [Algebra k Q] [Algebra.Smooth k R]
    [Fintype ι] [DecidableEq ι]
    (q : R →ₐ[k] Q) (hq : Function.Surjective q)
    (z : R) (hqz : q z = 0) (D : Derivation k R R) (hDz : D z = 1)
    (g : ι → R) (δ : ι → Derivation k Q Q)
    (hδ : ∀ i j, δ i (q (g j)) = if i = j then 1 else 0)
    (p : PrimeSpectrum R) (hqp : RingHom.ker q.toRingHom ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (f : R →ₐ[k] S),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
      ∃ (P : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom P = p ∧
      ∃ (n : ℕ) (φ : MvPolynomial (Fin n ⊕ Option ι) k →+* S), φ.Etale ∧
        (∀ c : k, φ (MvPolynomial.C c) = algebraMap k S c) ∧
        ∀ j, φ (MvPolynomial.X (Sum.inr j)) = f (AdaptedEtaleFrame.Construction.transverseExtendedCoordinates g z j) := by
  obtain ⟨A, hAk, hAs, f, hf, P, hP, E, hE⟩ :=
    quotient_dual_frame_lifts_to_pointed_open q hq z hqz D hDz g δ hδ p hqp
  obtain ⟨t, ht, n, φ, hφ, hφk, hX⟩ :=
    AdaptedEtaleFrame.Construction.exists_adapted_etale_frame E (fun j => f (AdaptedEtaleFrame.Construction.transverseExtendedCoordinates g z j)) hE P.asIdeal
  let S := Localization.Away t
  let a : A →ₐ[k] S := IsScalarTower.toAlgHom k A S
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := hf
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom a.toRingHom)) :=
    IsOpenImmersion.of_isLocalization t
  obtain ⟨P', hP'⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime t P ht
  refine ⟨.of S, inferInstance, a.comp f, ?_, P', ?_, n, φ, hφ, hφk, hX⟩
  · change IsOpenImmersion (Spec.map
      (CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom a.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  · apply PrimeSpectrum.ext
    change (P'.asIdeal.comap a.toRingHom).comap f.toRingHom = p.asIdeal
    have he : P'.asIdeal.comap a.toRingHom = P.asIdeal := congrArg PrimeSpectrum.asIdeal hP'
    rw [he]
    exact congrArg PrimeSpectrum.asIdeal hP

end

end OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientOpenFrame.Construction
