import OAI.AlgebraicGeometry.Resolution.Blowups.ReesLocalization

/-! # Homogeneous Localization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.HomogeneousLocalization.Construction

noncomputable section

/-! Homogeneous chart localization for the affine blowup gluing in Blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- An injective graded ring map induces an injective map on homogeneous
localizations away from corresponding homogeneous elements. -/
theorem homogeneousAway_map_injective
    {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (g : 𝒜 →+*ᵍ ℬ) (hg : Function.Injective g)
    {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) :
    Function.Injective (HomogeneousLocalization.Away.map g f) := by
  intro x y hxy
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf x
  obtain ⟨m, q, hq, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf y
  rw [HomogeneousLocalization.Away.map_mk, HomogeneousLocalization.Away.map_mk] at hxy
  have hv := congrArg (fun z : HomogeneousLocalization.Away ℬ (g f) => z.val) hxy
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hv
  obtain ⟨⟨_, ⟨k, rfl⟩⟩, hk⟩ := hv
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨f ^ k, ⟨k, rfl⟩⟩, hg ?_⟩
  simpa only [map_mul, map_pow] using hk

/-- The coefficient map represents a degree-zero element with denominator one. -/
theorem homogeneous_fromZero_val
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (P : Submonoid A) (x : 𝒜 0) :
    (HomogeneousLocalization.fromZeroRingHom 𝒜 P x).val =
      Localization.mk x.val (1 : P) := rfl

/-- Homogeneous chart maps commute with the degree-zero coefficient maps. -/
theorem homogeneousAway_map_fromZero
    {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (g : 𝒜 →+*ᵍ ℬ) (f : A) (x : 𝒜 0) :
    HomogeneousLocalization.Away.map g f
      (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) x) =
      HomogeneousLocalization.fromZeroRingHom ℬ (Submonoid.powers (g f))
        (g.gradedZeroRingHom x) := by
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.map g _
    (HomogeneousLocalization.mk ⟨0, x, 1, one_mem _⟩)).val =
    (HomogeneousLocalization.mk ⟨0, g.gradedZeroRingHom x, 1, one_mem _⟩).val
  rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_mk]
  refine congrArg₂ Localization.mk ?_ ?_
  · rfl
  · apply Subtype.ext
    change g (1 : A) = (1 : B)
    exact map_one g

/-- Degree-preserving denominator clearing gives localization on each
homogeneous chart, with no finiteness or smoothness assumptions. -/
theorem homogeneousAway_isLocalization_of_clearing
    {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (g : 𝒜 →+*ᵍ ℬ) (hg : Function.Injective g) (x : 𝒜 0)
    (hx : IsUnit (g.gradedZeroRingHom x))
    (hclear : ∀ (n : ℕ) (p : B), p ∈ ℬ n →
      ∃ (k : ℕ) (q : A), q ∈ 𝒜 n ∧ p * g x.val ^ k = g q)
    {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) :
    letI : Algebra (HomogeneousLocalization.Away 𝒜 f)
        (HomogeneousLocalization.Away ℬ (g f)) :=
      (HomogeneousLocalization.Away.map g f).toAlgebra
    IsLocalization.Away
      (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) x)
      (HomogeneousLocalization.Away ℬ (g f)) := by
  let : Algebra (HomogeneousLocalization.Away 𝒜 f)
      (HomogeneousLocalization.Away ℬ (g f)) :=
    (HomogeneousLocalization.Away.map g f).toAlgebra
  refine IsLocalization.Away.mk
    (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) x) ?_ ?_ ?_
  · change IsUnit (HomogeneousLocalization.Away.map g f
      (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) x))
    rw [homogeneousAway_map_fromZero]
    exact hx.map (HomogeneousLocalization.fromZeroRingHom ℬ (Submonoid.powers (g f)))
  · intro z
    obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective ℬ (g.map_mem hf) z
    obtain ⟨k, q, hq, heq⟩ := hclear (n • d) p hp
    refine ⟨k, HomogeneousLocalization.Away.mk 𝒜 hf n q hq, ?_⟩
    change HomogeneousLocalization.Away.mk ℬ (g.map_mem hf) n p hp *
        (HomogeneousLocalization.Away.map g f
          (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) x)) ^ k =
      HomogeneousLocalization.Away.map g f (HomogeneousLocalization.Away.mk 𝒜 hf n q hq)
    rw [homogeneousAway_map_fromZero, HomogeneousLocalization.Away.map_mk]
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
      homogeneous_fromZero_val ℬ (Submonoid.powers (g f)) (g.gradedZeroRingHom x),
      HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
      Localization.mk_pow, Localization.mk_mul]
    refine congrArg₂ Localization.mk ?_ ?_
    · exact heq
    · apply Subtype.ext
      simp
  · intro p q hpq
    have h : p = q := homogeneousAway_map_injective g hg hf hpq
    exact ⟨0, by simpa using h⟩

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R) (s : R) [IsLocalization.Away s S]

/-- Denominators can be cleared without changing the homogeneous degree
when the base is a domain and the localized element is nonzero. -/
theorem reesRingMap_clears_homogeneous [IsDomain R] (hs : s ≠ 0)
    (n : ℕ) (p : reesAlgebra (I.map (algebraMap R S)))
    (hp : p ∈ ReesGrading.Construction.reesGrade (I.map (algebraMap R S)) n) :
    ∃ (k : ℕ) (q : reesAlgebra I), q ∈ ReesGrading.Construction.reesGrade I n ∧
      p * ReesMap.Construction.reesRingMap I (algebraMap R S) (algebraMap R (reesAlgebra I) s) ^ k =
        ReesMap.Construction.reesRingMap I (algebraMap R S) q := by
  obtain ⟨k, q, hq⟩ := ReesLocalization.Construction.reesRingMap_clears_denominators I s p
  refine ⟨k, q, ?_, hq⟩
  have hx : algebraMap R (reesAlgebra I) s ∈ ReesGrading.Construction.reesGrade I 0 :=
    SetLike.algebraMap_mem_graded (ReesGrading.Construction.reesGrade I) s
  have hx' : ReesMap.Construction.reesRingMap I (algebraMap R S) (algebraMap R (reesAlgebra I) s) ∈
      ReesGrading.Construction.reesGrade (I.map (algebraMap R S)) 0 :=
    (ReesMap.Construction.reesGradedMap I (algebraMap R S)).map_mem hx
  have hpn : p * ReesMap.Construction.reesRingMap I (algebraMap R S) (algebraMap R (reesAlgebra I) s) ^ k ∈
      ReesGrading.Construction.reesGrade (I.map (algebraMap R S)) n := by
    simpa using SetLike.mul_mem_graded hp (SetLike.pow_mem_graded k hx')
  rw [hq] at hpn
  have hRS : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  intro m hm
  apply hRS
  have hc := hpn m hm
  change (q.val.map (algebraMap R S)).coeff m = 0 at hc
  simpa using hc

/-- The homogeneous chart maps induced by localizing the base are
localizations at the corresponding constant element. -/
theorem reesAwayMap_isLocalization [IsDomain R] (hs : s ≠ 0)
    {f : reesAlgebra I} {d : ℕ} (hf : f ∈ ReesGrading.Construction.reesGrade I d) :
    letI : Algebra (HomogeneousLocalization.Away (ReesGrading.Construction.reesGrade I) f)
        (HomogeneousLocalization.Away (ReesGrading.Construction.reesGrade (I.map (algebraMap R S)))
          (ReesMap.Construction.reesGradedMap I (algebraMap R S) f)) :=
      (HomogeneousLocalization.Away.map (ReesMap.Construction.reesGradedMap I (algebraMap R S)) f).toAlgebra
    IsLocalization.Away
      (HomogeneousLocalization.fromZeroRingHom (ReesGrading.Construction.reesGrade I) (Submonoid.powers f)
        ⟨algebraMap R (reesAlgebra I) s, SetLike.algebraMap_mem_graded (ReesGrading.Construction.reesGrade I) s⟩)
      (HomogeneousLocalization.Away (ReesGrading.Construction.reesGrade (I.map (algebraMap R S)))
        (ReesMap.Construction.reesGradedMap I (algebraMap R S) f)) := by
  have hRS : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  apply homogeneousAway_isLocalization_of_clearing
    (ReesMap.Construction.reesGradedMap I (algebraMap R S)) (ReesMap.Construction.reesRingMap_injective I (algebraMap R S) hRS)
    ⟨algebraMap R (reesAlgebra I) s, SetLike.algebraMap_mem_graded (ReesGrading.Construction.reesGrade I) s⟩
  · have hzero : (ReesMap.Construction.reesGradedMap I (algebraMap R S)).gradedZeroRingHom
        ⟨algebraMap R (reesAlgebra I) s, SetLike.algebraMap_mem_graded (ReesGrading.Construction.reesGrade I) s⟩ =
        algebraMap S (ReesGrading.Construction.reesGrade (I.map (algebraMap R S)) 0) (algebraMap R S s) := by
      apply Subtype.ext
      exact ReesMap.Construction.reesRingMap_constants I (algebraMap R S) s
    rw [hzero]
    exact (IsLocalization.Away.algebraMap_isUnit (S := S) s).map
      (algebraMap S (ReesGrading.Construction.reesGrade (I.map (algebraMap R S)) 0))
  · exact reesRingMap_clears_homogeneous I s hs
  · exact hf

end

end OAI.AlgebraicGeometry.Resolution.Blowups.HomogeneousLocalization.Construction
