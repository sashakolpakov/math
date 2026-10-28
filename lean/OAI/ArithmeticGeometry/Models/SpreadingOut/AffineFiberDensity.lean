import OAI.ArithmeticGeometry.Models.SpreadingOut.PrincipalDensityShrink

/-! # Affine Fiber Density -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.AffineFiberDensity.Construction

noncomputable section

/-! Density of affine opens in fibers of schemes over a Dedekind domain. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

theorem dense_basicOpen_of_mul_injective
    (B : Type u) [CommRing B] (b : B)
    (hb : Function.Injective (fun x : B ↦ b * x)) :
    Dense (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) := by
  have h := PrincipalFiberDensity.Construction.specMap_dominant_of_injective (algebraMap B (Localization.Away b))
    (FiberDomainTransfer.Construction.away_algebraMap_injective_of_mul_injective B b hb)
  have hd := (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))).denseRange
  change Dense (Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b)))) at hd
  rwa [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b] at hd

theorem affine_principalOpen_baseChange_dense
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (b : B)
    (hb : Function.Injective (fun x : S ⊗[R] B ↦ (1 ⊗ₜ[R] b) * x)) :
    Dense ((pullback.fst (Affine.Construction.affineOver R B).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⁻¹'
        (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B))) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let e := (Over.forget (Spec (.of S))).mapIso (Affine.Construction.baseChangeAffineIso R S B)
  have hp : e.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom) =
      pullback.fst (Affine.Construction.affineOver R B).hom g := by
    change ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R S B).hom) ≫ _ = _
    erw [Category.assoc, pullbackSpecIso_hom_snd, pullbackSymmetry_hom_comp_snd]
    rfl
  change Dense ((pullback.fst (Affine.Construction.affineOver R B).hom g) ⁻¹' _)
  rw [← hp]
  change Dense (e.hom ⁻¹' (PrimeSpectrum.basicOpen ((1 : S) ⊗ₜ[R] b) : Set (PrimeSpectrum (S ⊗[R] B))))
  exact (dense_basicOpen_of_mul_injective (S ⊗[R] B) (1 ⊗ₜ[R] b) hb).preimage e.hom.isOpenMap

theorem affine_open_dense_in_fibers_after_shrinking
    (R B : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra R B]
    (U : (Spec (.of B)).Opens) (hU : (U : Set (Spec (.of B))).Nonempty) :
    ∃ r : R, r ≠ 0 ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S], IsUnit (algebraMap R S r) →
        Dense ((pullback.fst (Affine.Construction.affineOver R B).hom
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⁻¹' (U : Set (Spec (.of B)))) := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨_, ⟨b, rfl⟩, hxb, hbU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx U.isOpen
  have hb : b ≠ 0 := by
    intro h
    change b ∉ x.asIdeal at hxb
    exact hxb (h ▸ x.asIdeal.zero_mem)
  obtain ⟨r, hr, hreg⟩ := PrincipalDensityShrink.Construction.tensor_regular_after_inverting_base_element R B b hb
  refine ⟨r, hr, fun S _ _ hu ↦ ?_⟩
  exact (affine_principalOpen_baseChange_dense R S B b (hreg S hu)).mono
    (Set.preimage_mono hbU)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.AffineFiberDensity.Construction
