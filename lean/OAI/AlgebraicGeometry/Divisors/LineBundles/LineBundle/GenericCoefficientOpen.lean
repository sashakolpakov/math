import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalCoefficient
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenCoefficient

/-! # Generic Coefficient Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: generic coefficients of actual restricted sections transform by the constructed open coefficient -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (i : Y ⟶ X) [IsOpenImmersion i]

theorem LineBundle.GenericCoefficientOpen.Cycles.openFunctionFieldMap_germ (U : Y.Opens) [Nonempty U] (r : Γ(X, i ''ᵁ U)) :
    RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i (X.germToFunctionField (i ''ᵁ U) r) =
      Y.germToFunctionField U ((i.appIso U).hom r) := by
  rw [Scheme.Hom.appIso_hom']
  exact ConcreteCategory.congr_hom
    (GenericFieldComposition.BundleCycles.genericFieldMap_germ_appLE i (genericPoint_eq_of_isOpenImmersion i)
      (i ''ᵁ U) U (i.preimage_image_eq U).ge) r

variable (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient_open_on_reference (U : Y.Opens) [Nonempty U]
    (hU : U ≤ L.openReferenceDomain i) (s : Γ((L.restrictToOpen i).sheaf, U)) :
    RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i
        (L.genericSectionCoefficient (i ''ᵁ U) ((L.sheaf.restrictAppIso i U).hom s)) =
      (L.openRationalCoefficient i).val * (L.restrictToOpen i).genericSectionCoefficient U s := by
  have hUX : i ''ᵁ U ≤ L.rationalReferenceOpen :=
    (i.image_mono hU).trans (L.openReferenceDomain_image i)
  rw [L.genericSectionCoefficient_eq_local (genericPoint X) (i ''ᵁ U) hUX,
    (L.restrictToOpen i).genericSectionCoefficient_eq_local (genericPoint Y) U (hU.trans inf_le_right)]
  unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalCoefficient
  rw [L.rationalSectionCoordinate_reference, (L.restrictToOpen i).rationalSectionCoordinate_reference]
  simp only [Units.val_one, div_one]
  rw [LineBundle.GenericCoefficientOpen.Cycles.openFunctionFieldMap_germ, L.openRationalCoefficient_on_open i U hU]
  change Y.germToFunctionField U (L.openSectionFrame i (genericPoint X) U hUX s) =
    Y.germToFunctionField U (L.openMixedTransitionOn i (genericPoint X) (genericPoint Y) U hUX
      (hU.trans inf_le_right)).val *
      Y.germToFunctionField U ((L.restrictToOpen i).sectionFrame (genericPoint Y) U (hU.trans inf_le_right) s)
  rw [← map_mul]
  exact congrArg (Y.germToFunctionField U) (LineBundle.FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_coordinates _ _ s)

omit [IsIntegral Y] in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient_restrictAppIso {U V : Y.Opens} [Nonempty U] [Nonempty V]
    (hVU : V ≤ U) (s : Γ((L.restrictToOpen i).sheaf, U)) :
    L.genericSectionCoefficient (i ''ᵁ V)
        ((L.sheaf.restrictAppIso i V).hom ((L.restrictToOpen i).sheaf.presheaf.map (homOfLE hVU).op s)) =
      L.genericSectionCoefficient (i ''ᵁ U) ((L.sheaf.restrictAppIso i U).hom s) := by
  have h := Scheme.Modules.map_restrictAppIso_hom_apply i L.sheaf (homOfLE hVU).op s
  exact (congrArg (L.genericSectionCoefficient (i ''ᵁ V)) h).trans
    (L.genericSectionCoefficient_restrict (i.image_mono hVU) _)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient_open (U : Y.Opens) [Nonempty U]
    (s : Γ((L.restrictToOpen i).sheaf, U)) :
    RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i
        (L.genericSectionCoefficient (i ''ᵁ U) ((L.sheaf.restrictAppIso i U).hom s)) =
      (L.openRationalCoefficient i).val * (L.restrictToOpen i).genericSectionCoefficient U s := by
  let V : Y.Opens := U ⊓ L.openReferenceDomain i
  let : Nonempty V := ⟨⟨genericPoint Y,
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›),
    ((genericPoint_spec Y).mem_open_set_iff (L.openReferenceDomain i).isOpen).mpr
      (by simpa using (inferInstance : Nonempty (L.openReferenceDomain i)))⟩⟩
  have hVU : V ≤ U := inf_le_left
  let t := (L.restrictToOpen i).sheaf.presheaf.map (homOfLE hVU).op s
  calc
    _ = RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i (L.genericSectionCoefficient (i ''ᵁ V)
        ((L.sheaf.restrictAppIso i V).hom t)) :=
      congrArg (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i) (L.genericSectionCoefficient_restrictAppIso i hVU s).symm
    _ = (L.openRationalCoefficient i).val * (L.restrictToOpen i).genericSectionCoefficient V t :=
      L.genericSectionCoefficient_open_on_reference i V inf_le_right t
    _ = _ := congrArg (fun z => (L.openRationalCoefficient i).val * z)
      ((L.restrictToOpen i).genericSectionCoefficient_restrict hVU s)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
