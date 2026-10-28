import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Data
import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedBlowupSmoothGluing
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Map Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapGluing.Construction

noncomputable section

/-! Gluing actual maps from local Rees blowups through affine overlap comparisons. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
variable (I : X.IdealSheafData) (hI : I ≠ ⊥)

theorem globalBlowupChart_opensRange (U : X.affineOpens) :
    (Data.Construction.globalBlowupChart I hI U).opensRange = Data.Construction.globalBlowupToBase I hI ⁻¹ᵁ U.1 := by
  have h := SupportedBlowupSmoothGluing.Construction.opensRange_of_open_pullback (Data.Construction.globalBlowupChart I hI U)
    (ReesGrading.Construction.affineBlowupToSpec (I.ideal U) ≫ U.2.isoSpec.inv)
    (Data.Construction.globalBlowupToBase I hI) U.1.ι (Data.Construction.globalBlowup_affineOpen_isPullback I hI U)
  rwa [Scheme.Opens.opensRange_ι] at h

theorem globalBlowup_affineSpec_isPullback (U : X.affineOpens) :
    IsPullback (Data.Construction.globalBlowupChart I hI U) (ReesGrading.Construction.affineBlowupToSpec (I.ideal U))
      (Data.Construction.globalBlowupToBase I hI) U.2.fromSpec := by
  apply (Data.Construction.globalBlowup_affineOpen_isPullback I hI U).of_iso
    (Iso.refl _) (Iso.refl _) U.2.isoSpec (Iso.refl _)
  · simp
  · simp
  · simp
  · simp [IsAffineOpen.fromSpec]

/-- Any chosen affine cover of the base gives an actual open cover of its global blowup. -/
def globalBlowupChosenCover {ι : Type*} (U : ι → X.affineOpens)
    (hcover : ⨆ i, (U i).1 = ⊤) : (Data.Construction.globalBlowup I hI).OpenCover := by
  refine Scheme.Cover.mkOfCovers ι (fun i => ReesGrading.Construction.affineBlowup (I.ideal (U i)))
    (fun i => Data.Construction.globalBlowupChart I hI (U i)) ?_ (fun _ => inferInstance)
  intro z
  have hz : Data.Construction.globalBlowupToBase I hI z ∈ ⨆ i, (U i).1 := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  refine ⟨i, ?_⟩
  change z ∈ (Data.Construction.globalBlowupChart I hI (U i)).opensRange
  rw [globalBlowupChart_opensRange]
  exact hi

/-- Compatibility on affine opens inside the intersection implies compatibility
on the actual scheme-theoretic overlap of the two blowup charts. -/
theorem globalBlowupChart_overlap_map_eq
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    {Y : Scheme} (p : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType p] [IsSeparated p]
    (U V : X.affineOpens) (qU : ReesGrading.Construction.affineBlowup (I.ideal U) ⟶ Y)
    (qV : ReesGrading.Construction.affineBlowup (I.ideal V) ⟶ Y)
    (hoU : qU ≫ p = Data.Construction.globalBlowupChart I hI U ≫ Data.Construction.globalBlowupToBase I hI ≫ f)
    (hoV : qV ≫ p = Data.Construction.globalBlowupChart I hI V ≫ Data.Construction.globalBlowupToBase I hI ≫ f)
    (hc : ∀ (W : X.affineOpens) (hWU : W ≤ U) (hWV : W ≤ V),
      (Blowup.Functor.Construction.idealBlowupFunctor I).map (homOfLE hWU) ≫ qU =
        (Blowup.Functor.Construction.idealBlowupFunctor I).map (homOfLE hWV) ≫ qV) :
    pullback.fst (Data.Construction.globalBlowupChart I hI U) (Data.Construction.globalBlowupChart I hI V) ≫ qU =
      pullback.snd _ _ ≫ qV := by
  let a := Data.Construction.globalBlowupChart I hI U
  let b := Data.Construction.globalBlowupChart I hI V
  let k := pullback.fst a b ≫ a
  let : IsReduced (pullback a b) := isReduced_of_isOpenImmersion k
  let : LocallyOfFiniteType ((pullback.fst a b ≫ qU) ≫ p) := by
    rw [Category.assoc, hoU]
    infer_instance
  apply ext_of_apply_eq p Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro z _ _
    let y := a (pullback.fst a b z)
    have hyj : y = b (pullback.snd a b z) :=
      congrArg (fun g : pullback a b ⟶ Data.Construction.globalBlowup I hI => g z) (pullback.condition (f := a) (g := b))
    have hyU : Data.Construction.globalBlowupToBase I hI y ∈ U.1 := by
      have hy : y ∈ a.opensRange := ⟨pullback.fst a b z, rfl⟩
      change y ∈ (Data.Construction.globalBlowupChart I hI U).opensRange at hy
      rwa [globalBlowupChart_opensRange] at hy
    have hyV : Data.Construction.globalBlowupToBase I hI y ∈ V.1 := by
      have hy : y ∈ b.opensRange := ⟨pullback.snd a b z, hyj.symm⟩
      change y ∈ (Data.Construction.globalBlowupChart I hI V).opensRange at hy
      rwa [globalBlowupChart_opensRange] at hy
    obtain ⟨W, hW, hyW, hWUV⟩ := exists_isAffineOpen_mem_and_subset
      (U := U.1 ⊓ V.1) (x := Data.Construction.globalBlowupToBase I hI y) ⟨hyU, hyV⟩
    let A : X.affineOpens := ⟨W, hW⟩
    have hAU : A ≤ U := hWUV.trans inf_le_left
    have hAV : A ≤ V := hWUV.trans inf_le_right
    have hyA : y ∈ (Data.Construction.globalBlowupChart I hI A).opensRange := by
      rw [globalBlowupChart_opensRange]
      exact hyW
    obtain ⟨w, hw⟩ := hyA
    let α := (Blowup.Functor.Construction.idealBlowupFunctor I).map (homOfLE hAU)
    let β := (Blowup.Functor.Construction.idealBlowupFunctor I).map (homOfLE hAV)
    have hα : α w = pullback.fst a b z := by
      apply a.injective
      change (α ≫ Data.Construction.globalBlowupChart I hI U) w = y
      rw [Data.Construction.globalBlowupChart_transition]
      exact hw
    have hβ : β w = pullback.snd a b z := by
      apply b.injective
      change (β ≫ Data.Construction.globalBlowupChart I hI V) w = b (pullback.snd a b z)
      rw [Data.Construction.globalBlowupChart_transition]
      exact hw.trans hyj
    change qU (pullback.fst a b z) = qV (pullback.snd a b z)
    rw [← hα, ← hβ]
    exact congrArg (fun g : ReesGrading.Construction.affineBlowup (I.ideal A) ⟶ Y => g w) (hc A hAU hAV)
  · rw [Category.assoc, Category.assoc, hoU, hoV]
    exact pullback.condition_assoc (f := a) (g := b) (Data.Construction.globalBlowupToBase I hI ≫ f)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapGluing.Construction
