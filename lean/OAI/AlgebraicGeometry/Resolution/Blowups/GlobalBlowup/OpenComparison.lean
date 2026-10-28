import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtaleBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenTransport

/-! # Open Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenComparison.Construction

noncomputable section

section

/-! Canonical global comparison maps agree with the actual open blowup squares. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {V X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral V] [IsLocallyNoetherian V] (j : V ⟶ X) [IsOpenImmersion j]

theorem globalBlowupMapTo_eq_openMapTo
    (I : X.IdealSheafData) (L : V.IdealSheafData) (he : I.comap j = L) (hI : I ≠ ⊥) (hL : L ≠ ⊥) :
    SpecifiedMap.Construction.globalBlowupMapTo j I L he hI hL = OpenTransport.Construction.globalBlowupOpenMapTo j I hI L hL he := by
  subst L
  exact FunctorialMap.Construction.globalBlowupMap_eq_openMap j I hI hL

instance globalBlowupMapTo_isOpenImmersion
    (I : X.IdealSheafData) (L : V.IdealSheafData) (he : I.comap j = L) (hI : I ≠ ⊥) (hL : L ≠ ⊥) :
    IsOpenImmersion (SpecifiedMap.Construction.globalBlowupMapTo j I L he hI hL) := by
  exact (globalBlowupMapTo_eq_openMapTo j I L he hI hL).symm ▸
    (inferInstanceAs (IsOpenImmersion (OpenTransport.Construction.globalBlowupOpenMapTo j I hI L hL he)))

theorem globalBlowupMapTo_contains_order_support
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I J : X.IdealSheafData) (hI : I ≠ ⊥)
    (L : V.IdealSheafData) (hL : L ≠ ⊥) (he : I.comap j = L)
    (b : ℕ) (hb : 0 < b) (hp : J ≤ I ^ b) [Smooth (Data.Construction.globalBlowupToBase I hI ≫ f)]
    (hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support : Set X) ⊆ Set.range j) :
    ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) (b - 1)).support : Set (Data.Construction.globalBlowup I hI)) ⊆
      Set.range (SpecifiedMap.Construction.globalBlowupMapTo j I L he hI hL) := by
  rw [globalBlowupMapTo_eq_openMapTo]
  exact OpenTransport.Construction.globalBlowupOpenMapTo_contains_order_support j f I J hI L hL he b hb hp hcover

end

/-! The actual local blowups of a global center form an open cover of the global blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

instance globalBlowupMapTo_quasiCompact
    {V : Scheme} [IsIntegral V] [IsLocallyNoetherian V]
    (q : V ⟶ X) [Etale q] [QuasiCompact q]
    (I : X.IdealSheafData) (K : V.IdealSheafData)
    (he : I.comap q = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥) :
    QuasiCompact (SpecifiedMap.Construction.globalBlowupMapTo q I K he hI hK) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact)
    (EtalePullback.Construction.globalBlowupMapTo_etale_isPullback q I K he hI hK).flip inferInstance

def globalBlowupOpenCover (I : X.IdealSheafData) (hI : I ≠ ⊥) (C : X.OpenCover)
    [∀ i, IsIntegral (C.X i)] [∀ i, IsLocallyNoetherian (C.X i)]
    (K : ∀ i, (C.X i).IdealSheafData) (hK : ∀ i, K i ≠ ⊥) (he : ∀ i, I.comap (C.f i) = K i) :
    (Data.Construction.globalBlowup I hI).OpenCover := by
  apply Scheme.Cover.mkOfCovers C.I₀ (fun i => Data.Construction.globalBlowup (K i) (hK i))
    (fun i => SpecifiedMap.Construction.globalBlowupMapTo (C.f i) I (K i) (he i) hI (hK i))
  · intro x
    obtain ⟨i, y, hy⟩ := C.exists_eq (Data.Construction.globalBlowupToBase I hI x)
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
      (EtalePullback.Construction.globalBlowupMapTo_etale_isPullback (C.f i) I (K i) (he i) hI (hK i)) x y hy.symm
    exact ⟨i, z, hz⟩

theorem globalBlowup_smooth_of_open_blowups (I : X.IdealSheafData) (hI : I ≠ ⊥) (C : X.OpenCover)
    [∀ i, IsIntegral (C.X i)] [∀ i, IsLocallyNoetherian (C.X i)]
    (K : ∀ i, (C.X i).IdealSheafData) (hK : ∀ i, K i ≠ ⊥) (he : ∀ i, I.comap (C.f i) = K i)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (hs : ∀ i, Smooth (Data.Construction.globalBlowupToBase (K i) (hK i) ≫ (C.f i ≫ f))) :
    Smooth (Data.Construction.globalBlowupToBase I hI ≫ f) := by
  let : IsZariskiLocalAtSource @Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth) (globalBlowupOpenCover I hI C K hK he)
  intro i
  change C.I₀ at i
  change Smooth (SpecifiedMap.Construction.globalBlowupMapTo (C.f i) I (K i) (he i) hI (hK i) ≫ (Data.Construction.globalBlowupToBase I hI ≫ f))
  rw [← Category.assoc, SpecifiedMap.Construction.globalBlowupMapTo_over, Category.assoc]
  exact hs i

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenComparison.Construction
