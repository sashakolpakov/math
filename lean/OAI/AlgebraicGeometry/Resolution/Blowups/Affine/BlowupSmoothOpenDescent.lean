import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.FlatBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedBlowupSmoothGluing
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Blowup Smooth Open Descent -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupSmoothOpenDescent.Construction

noncomputable section

/-! Smoothness of an actual affine blowup descends from pointed open changes of its base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineBlowupMap_open_of_spec_open
    {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R) (φ : R →+* S)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))] :
    IsOpenImmersion (ReesMap.Construction.affineBlowupMap I φ) := by
  let : Algebra R S := φ.toAlgebra
  have he : φ.Etale := by
    exact (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom φ)).mp inferInstance
  let : Algebra.Etale R S := RingHom.etale_algebraMap.mp he
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (Blowup.FlatBaseChange.Construction.affineBlowup_flat_isPullback (S := S) I).flip inferInstance

theorem affineBlowup_smooth_of_pointed_open_bases
    (k : Type u) [CommRing k] {R : Type u} [CommRing R] [Algebra k R] (I : Ideal R)
    (hlocal : ∀ p : PrimeSpectrum R,
      ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (f : R →ₐ[k] S),
        IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
        ∃ q : PrimeSpectrum S, PrimeSpectrum.comap f.toRingHom q = p ∧
          Smooth (ReesGrading.Construction.affineBlowupToSpec (I.map f.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap k S)))) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  choose S alg f hopen q hq hs using hlocal
  let : ∀ p, Algebra k (S p) := alg
  let : ∀ p, IsOpenImmersion (Spec.map (CommRingCat.ofHom (f p).toRingHom)) := hopen
  let F (p : PrimeSpectrum R) := ReesMap.Construction.affineBlowupMap I (f p).toRingHom
  let : ∀ p, IsOpenImmersion (F p) := fun p => affineBlowupMap_open_of_spec_open I (f p).toRingHom
  have hcover : ⨆ p, (F p).opensRange = ⊤ := by
    apply top_le_iff.mp
    intro y _
    let p : PrimeSpectrum R := ReesGrading.Construction.affineBlowupToSpec I y
    let : Algebra k (S p) := alg p
    let : Algebra R (S p) := (f p).toRingHom.toAlgebra
    have he : (f p).toRingHom.Etale := by
      exact (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom (f p).toRingHom)).mp inferInstance
    let : Algebra.Etale R (S p) := RingHom.etale_algebraMap.mp he
    have hpb : IsPullback (F p) (ReesGrading.Construction.affineBlowupToSpec (I.map (f p).toRingHom))
        (ReesGrading.Construction.affineBlowupToSpec I) (Spec.map (CommRingCat.ofHom (f p).toRingHom)) :=
      Blowup.FlatBaseChange.Construction.affineBlowup_flat_isPullback (S := S p) I
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback hpb y (q p) (hq p).symm
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, z, hz⟩
  let g := ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))
  have hcomp (p : PrimeSpectrum R) : F p ≫ g =
      ReesGrading.Construction.affineBlowupToSpec (I.map (f p).toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap k (S p))) := by
    have hground : Spec.map (CommRingCat.ofHom (f p).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k R)) =
          Spec.map (CommRingCat.ofHom (algebraMap k (S p))) := by
      rw [← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom ((f p).toRingHom.comp (algebraMap k R))) = _
      exact congrArg (fun φ : k →+* S p => Spec.map (CommRingCat.ofHom φ)) (RingHom.ext (f p).commutes)
    change ReesMap.Construction.affineBlowupMap I (f p).toRingHom ≫
      (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) = _
    rw [← Category.assoc, Blowup.BaseOpen.Construction.affineBlowupMap_over, Category.assoc, hground]
  let : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth) (fun p => (F p).opensRange) hcover
  intro p
  let : Smooth (F p ≫ g) := (hcomp p).symm ▸ hs p
  exact SupportedBlowupSmoothGluing.Construction.smooth_on_opensRange_of_open_immersion g (F p)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupSmoothOpenDescent.Construction
