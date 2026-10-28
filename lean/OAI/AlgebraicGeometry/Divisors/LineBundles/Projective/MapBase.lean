import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Map Base -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapBase.BundleCycles

noncomputable section

/-! Native Proj maps commute with the actual degree-zero structure map. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

universe u

section Rings

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)

theorem gradedAwayMap_fromZero (s : A) (a : 𝒜 0) :
    Away.map f s (fromZeroRingHom 𝒜 (Submonoid.powers s) a) =
      fromZeroRingHom ℬ (Submonoid.powers (f s)) (f.gradedZeroRingHom a) := by
  change HomogeneousLocalization.map f _ (HomogeneousLocalization.mk ⟨0, a, 1, by simp⟩) =
    HomogeneousLocalization.mk ⟨0, f.gradedZeroRingHom a, 1, by simp⟩
  rw [HomogeneousLocalization.map_mk]
  congr 1
  apply HomogeneousLocalization.NumDenSameDeg.ext
  · rfl
  · rfl
  · exact map_one f

end Rings

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)

theorem projectiveMap_toSpecZero
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  let n : ℕ := s.1.val
  let a : A := s.2.val
  have hn : 0 < n := s.1.property
  have ha : a ∈ 𝒜 n := s.2.property
  change Proj.awayι ℬ (f a) (f.map_mem ha) hn ≫ (Proj.map f hf ≫ Proj.toSpecZero 𝒜) =
    Proj.awayι ℬ (f a) (f.map_mem ha) hn ≫
      (Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom))
  have hmap := Proj.awayι_comp_map f hf hn a ha
  rw [← Category.assoc, hmap, Category.assoc, Proj.awayι_toSpecZero,
    ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext z
  exact congrArg HomogeneousLocalization.val (gradedAwayMap_fromZero f a z)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapBase.BundleCycles
