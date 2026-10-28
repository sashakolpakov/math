import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericCoefficientOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericCoefficientIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.OpenSectionPullback

/-! # Open Pullback Coefficient -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: actual open pullback of a rational section and its exact divisor -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (i : Y ⟶ X) [IsOpenImmersion i]

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openPullbackSectionCoefficient (a : X.functionFieldˣ) : Y.functionFieldˣ :=
  LineBundle.OpenDivisor.Cycles.lineBundleIsoSectionCoefficient (L.restrictToOpenPullbackIso i) (L.openSectionCoefficient i a)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openPullback_section_divisor (a : X.functionFieldˣ) :
    (L.pullback i).rationalSectionPointDivisorWithCoefficient (L.openPullbackSectionCoefficient i a) =
      Finsupp.comapDomain i (L.rationalSectionPointDivisorWithCoefficient a) i.isOpenEmbedding.injective.injOn := by
  unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openPullbackSectionCoefficient
  rw [LineBundle.OpenDivisor.Cycles.lineBundleIso_section_divisor, L.open_section_divisor i a]

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient_openPullback (a : X.functionFieldˣ)
    (U : X.Opens) [Nonempty U] (V : Y.Opens) [Nonempty V] (hV : V ≤ i ⁻¹ᵁ U)
    (s : Γ(L.sheaf, U)) (hs : L.genericSectionCoefficient U s = a.val) :
    (L.pullback i).genericSectionCoefficient V (Module.SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen i L.sheaf U V hV s) =
      (L.openPullbackSectionCoefficient i a).val := by
  let hUV : i ''ᵁ V ≤ U := (i.image_mono hV).trans (i.image_preimage_le U)
  let t : Γ((L.restrictToOpen i).sheaf, V) :=
    (L.sheaf.restrictAppIso i V).inv (L.sheaf.presheaf.map (homOfLE hUV).op s)
  have ht : L.genericSectionCoefficient (i ''ᵁ V) ((L.sheaf.restrictAppIso i V).hom t) = a.val := by
    change L.genericSectionCoefficient (i ''ᵁ V)
      ((L.sheaf.restrictAppIso i V).hom ((L.sheaf.restrictAppIso i V).inv _)) = _
    rw [Iso.inv_hom_id_apply]
    exact (L.genericSectionCoefficient_restrict hUV s).trans hs
  have ho := L.genericSectionCoefficient_open i V t
  rw [ht] at ho
  have hc : (L.restrictToOpen i).genericSectionCoefficient V t =
      (L.openSectionCoefficient i a).val := by
    unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openSectionCoefficient
    rw [Units.val_div_eq_div_val]
    apply (eq_div_iff (L.openRationalCoefficient i).ne_zero).mpr
    exact (mul_comm _ _).trans ho.symm
  have hp := Module.OpenSectionPullback.BundleCycles.moduleOpenPullbackIso_toOpen i L.sheaf U V hV s
  have hi := LineBundle.GenericCoefficientIso.Cycles.genericSectionCoefficient_iso (L.restrictToOpenPullbackIso i) V t
  calc
    _ = (L.pullback i).genericSectionCoefficient V ((L.restrictToOpenPullbackIso i).hom.app V t) :=
      congrArg ((L.pullback i).genericSectionCoefficient V) hp.symm
    _ = (LineBundle.IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient (L.restrictToOpenPullbackIso i)).val *
        (L.restrictToOpen i).genericSectionCoefficient V t := hi
    _ = _ := by rw [hc]; exact mul_comm _ _

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient_openPullback_onOpen (a : X.functionFieldˣ)
    (U : X.Opens) [Nonempty U] [Nonempty (i ⁻¹ᵁ U)]
    (s : Γ(L.sheaf, U)) (hs : L.genericSectionCoefficient U s = a.val) :
    (L.pullback i).genericSectionCoefficient (i ⁻¹ᵁ U) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen i L.sheaf U s) =
      (L.openPullbackSectionCoefficient i a).val :=
  ((L.pullback i).genericSectionCoefficient_restrict le_rfl _).symm.trans
    (L.genericSectionCoefficient_openPullback i a U (i ⁻¹ᵁ U) le_rfl s hs)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
