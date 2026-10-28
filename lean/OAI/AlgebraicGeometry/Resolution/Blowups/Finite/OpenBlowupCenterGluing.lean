import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.OpenIdealSheafGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PointedSmoothCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenComparison

/-! # Open Blowup Center Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.OpenBlowupCenterGluing.Construction

noncomputable section

/-! Compatible local permissible blowup steps construct a global smooth center and its actual smooth blowup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem exists_global_blowup_center_of_finite_open_data
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (J : X.IdealSheafData) (b : ℕ) (C : X.OpenCover) [Finite C.I₀]
    [∀ i, IsIntegral (C.X i)] [∀ i, IsLocallyNoetherian (C.X i)] [∀ i, QuasiCompact (C.f i)]
    (K : ∀ i, (C.X i).IdealSheafData) (hK : ∀ i, K i ≠ ⊥)
    (hp : ∀ i, J.comap (C.f i) ≤ K i ^ b)
    (hs : ∀ i, Smooth ((K i).subschemeι ≫ (C.f i ≫ f)))
    (hbl : ∀ i, Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase (K i) (hK i) ≫ (C.f i ≫ f)))
    (hcompat : ∀ i j, (K i).comap (pullback.fst (C.f i) (C.f j)) =
      (K j).comap (pullback.snd (C.f i) (C.f j))) :
    ∃ (I : X.IdealSheafData) (hI : I ≠ ⊥),
      (∀ i, I.comap (C.f i) = K i) ∧ J ≤ I ^ b ∧ Smooth (I.subschemeι ≫ f) ∧
        Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := by
  classical
  obtain ⟨I, he⟩ := OpenIdealSheafGluing.Construction.exists_idealSheaf_of_finite_open_compatibility C.X C.f K hcompat
  have hI : I ≠ ⊥ := by
    intro hz
    obtain ⟨i, _, _⟩ := C.exists_eq (Classical.choice (inferInstance : Nonempty X))
    apply hK i
    rw [← he i, hz, Scheme.IdealSheafData.comap_bot]
  have hperm : J ≤ I ^ b := by
    apply IdealSheaf.EqualityGluing.Construction.idealSheaf_le_of_openCover J (I ^ b) C
    intro i
    rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, he i]
    exact hp i
  have hcenter : Smooth (I.subschemeι ≫ f) := by
    apply Global.PointedSmoothCenter.Construction.idealSheaf_subscheme_smooth_of_open_charts I f C.X C.f C.iSup_opensRange
    intro i
    rw [he i]
    exact hs i
  exact ⟨I, hI, he, hperm, hcenter, GlobalBlowup.OpenComparison.Construction.globalBlowup_smooth_of_open_blowups I hI C K hK he f hbl⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.OpenBlowupCenterGluing.Construction
