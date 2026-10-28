import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapBase

/-! # Scalar Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ScalarOpen.BundleCycles

noncomputable section

/-! The actual Proj structure map contracts a homogeneous prime to its
degree-zero part. This identifies scalar nonvanishing opens. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem projectiveBasicOpenToSpec_native (s : A) :
    (Proj.basicOpenToSpec 𝒜 s).toLRSHom = ProjectiveSpectrum.Proj.toSpec 𝒜 s := by
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

theorem projectiveBasicOpenToSpec_mem (s : A) (p : (Proj.basicOpen 𝒜 s).toScheme)
    (z : NumDenSameDeg 𝒜 (Submonoid.powers s)) :
    HomogeneousLocalization.mk z ∈ (Proj.basicOpenToSpec 𝒜 s p).asIdeal ↔ z.num.val ∈ p.val.asHomogeneousIdeal := by
  have h := ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 p z
  have he := congrArg (fun j => j.base p) (projectiveBasicOpenToSpec_native 𝒜 s)
  exact (congrArg (fun q : PrimeSpectrum (Away 𝒜 s) => HomogeneousLocalization.mk z ∈ q.asIdeal) he).to_iff.trans h

theorem projectiveToSpecZero_mem (p : Proj 𝒜) (a : 𝒜 0) :
    a ∈ (Proj.toSpecZero 𝒜 p).asIdeal ↔ a.val ∈ p.asHomogeneousIdeal := by
  let t : Proj 𝒜 ⟶ (Proj.basicOpen 𝒜 1).toScheme :=
    (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ (Proj.basicOpen_one 𝒜)).inv
  have ht : t ≫ (Proj.basicOpen 𝒜 1).ι = 𝟙 (Proj 𝒜) := by
    change ((Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ (Proj.basicOpen_one 𝒜)).inv) ≫ _ = _
    rw [Category.assoc, Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι]
  let q : (Proj.basicOpen 𝒜 1).toScheme := t p
  have hq : q.val = p := congrArg (fun j : Proj 𝒜 ⟶ Proj 𝒜 => j p) ht
  change HomogeneousLocalization.mk ⟨0, a, 1, by simp⟩ ∈
    (Proj.basicOpenToSpec 𝒜 1 q).asIdeal ↔ a.val ∈ p.asHomogeneousIdeal
  exact (projectiveBasicOpenToSpec_mem 𝒜 1 q _).trans
    (congrArg (fun z : Proj 𝒜 => a.val ∈ z.asHomogeneousIdeal) hq).to_iff

theorem projectiveToSpecZero_preimage (a : 𝒜 0) :
    Proj.toSpecZero 𝒜 ⁻¹ᵁ (PrimeSpectrum.basicOpen a : (Spec (.of (𝒜 0))).Opens) =
      Proj.basicOpen 𝒜 a.val := by
  ext p
  exact not_congr (projectiveToSpecZero_mem 𝒜 p a)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ScalarOpen.BundleCycles
