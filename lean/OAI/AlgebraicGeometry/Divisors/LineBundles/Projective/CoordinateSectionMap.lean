import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartRegular
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularRingEquiv
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Coordinate Section Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.CoordinateSectionMap.BundleCycles

noncomputable section

section

/-! Actual degree-zero fractions of linear homogeneous coordinates
give regular functions on projective charts and satisfy their cross identities. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

def projectiveCoordinateSection (v t : A) (hv : v ∈ 𝒜 1) (ht : t ∈ 𝒜 1) :
    Γ(Proj 𝒜, Proj.basicOpen 𝒜 v) :=
  Proj.awayToSection 𝒜 v (Away.mk 𝒜 hv 1 t (by simpa only [one_smul] using ht))

theorem projectiveCoordinateSection_value (v t : A) (hv : v ∈ 𝒜 1) (ht : t ∈ 𝒜 1)
    (x : Proj.basicOpen 𝒜 v) :
    ((projectiveCoordinateSection 𝒜 v t hv ht).val x).val =
      Localization.mk t ⟨v, x.property⟩ := by
  change Localization.mk t ⟨v ^ 1, _⟩ = Localization.mk t ⟨v, _⟩
  congr 1
  exact Subtype.ext (pow_one v)

theorem projectiveCoordinateSection_regular (v t : A) (hv : v ∈ 𝒜 1) (ht : t ∈ 𝒜 1)
    (hreg : IsRegular t) : IsRegular (projectiveCoordinateSection 𝒜 v t hv ht) := by
  exact RegularRingEquiv.BundleCycles.regular_ringEquiv (Proj.basicOpenIsoAway 𝒜 v hv (by decide)).commRingCatIsoToRingEquiv
    (Away.mk 𝒜 hv 1 t (by simpa only [one_smul] using ht))
    (Graded.ChartRegular.BundleCycles.gradedAway_mk_isRegular 𝒜 hv 1 t _ hreg)

theorem projectiveCoordinateSection_cross (v w t u : A)
    (hv : v ∈ 𝒜 1) (hw : w ∈ 𝒜 1) (ht : t ∈ 𝒜 1) (hu : u ∈ 𝒜 1)
    (U : (Proj 𝒜).Opens) (hUv : U ≤ Proj.basicOpen 𝒜 v) (hUw : U ≤ Proj.basicOpen 𝒜 w) :
    (Proj 𝒜).presheaf.map (homOfLE hUv).op (projectiveCoordinateSection 𝒜 v t hv ht) *
        (Proj 𝒜).presheaf.map (homOfLE hUw).op (projectiveCoordinateSection 𝒜 w u hw hu) =
      (Proj 𝒜).presheaf.map (homOfLE hUv).op (projectiveCoordinateSection 𝒜 v u hv hu) *
        (Proj 𝒜).presheaf.map (homOfLE hUw).op (projectiveCoordinateSection 𝒜 w t hw ht) := by
  apply Subtype.ext
  funext x
  let y : ProjectiveSpectrum 𝒜 := x.1
  let : x.1.asHomogeneousIdeal.toIdeal.IsPrime :=
    inferInstanceAs (y.asHomogeneousIdeal.toIdeal.IsPrime)
  let ev : Γ(Proj 𝒜, U) →+* HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal :=
    (AlgebraicGeometry.openToLocalization 𝒜 U x.1 x.2).hom
  change ev ((Proj 𝒜).presheaf.map (homOfLE hUv).op (projectiveCoordinateSection 𝒜 v t hv ht) *
      (Proj 𝒜).presheaf.map (homOfLE hUw).op (projectiveCoordinateSection 𝒜 w u hw hu)) =
    ev ((Proj 𝒜).presheaf.map (homOfLE hUv).op (projectiveCoordinateSection 𝒜 v u hv hu) *
      (Proj 𝒜).presheaf.map (homOfLE hUw).op (projectiveCoordinateSection 𝒜 w t hw ht))
  rw [map_mul, map_mul]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mul]
  change ((projectiveCoordinateSection 𝒜 v t hv ht).val ⟨x.1, hUv x.2⟩).val *
      ((projectiveCoordinateSection 𝒜 w u hw hu).val ⟨x.1, hUw x.2⟩).val =
    ((projectiveCoordinateSection 𝒜 v u hv hu).val ⟨x.1, hUv x.2⟩).val *
      ((projectiveCoordinateSection 𝒜 w t hw ht).val ⟨x.1, hUw x.2⟩).val
  have h₁ := projectiveCoordinateSection_value 𝒜 v t hv ht ⟨x.1, hUv x.2⟩
  have h₂ := projectiveCoordinateSection_value 𝒜 w u hw hu ⟨x.1, hUw x.2⟩
  have h₃ := projectiveCoordinateSection_value 𝒜 v u hv hu ⟨x.1, hUv x.2⟩
  have h₄ := projectiveCoordinateSection_value 𝒜 w t hw ht ⟨x.1, hUw x.2⟩
  refine (congrArg₂ (fun a b => a * b) h₁ h₂).trans (Eq.trans ?_
    (congrArg₂ (fun a b => a * b) h₃ h₄).symm)
  rw [Localization.mk_mul, Localization.mk_mul, mul_comm t u]

end

/-! Pullback of actual homogeneous coordinate fractions is the
fraction of the mapped coordinates on the corresponding projective chart. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

theorem projectiveCoordinateSection_map
    {A B σ τ : Type} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (v t : A) (hv : v ∈ 𝒜 1) (ht : t ∈ 𝒜 1) :
    (Proj.map f hf).app (Proj.basicOpen 𝒜 v) (projectiveCoordinateSection 𝒜 v t hv ht) =
      projectiveCoordinateSection ℬ (f v) (f t) (f.map_mem hv) (f.map_mem ht) := by
  have H := ConcreteCategory.congr_hom (Proj.awayToSection_comp_appLE f hf hv)
    (Away.mk 𝒜 hv 1 t (by simpa only [one_smul] using ht))
  have hm := Away.map_mk f v hv 1 t (by simpa only [one_smul] using ht)
  exact H.trans (congrArg (Proj.awayToSection ℬ (f v)) hm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.CoordinateSectionMap.BundleCycles
