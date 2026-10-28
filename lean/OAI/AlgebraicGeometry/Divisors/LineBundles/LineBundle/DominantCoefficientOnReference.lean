import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantReferencePullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericCoefficientScalar

/-! # Dominant Coefficient On Reference -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

section

/-! # LineBundleCycles: actual dominant pullback scales generic coefficients by the pulled reference generator -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient_dominant_on_reference (U : Y.Opens) [Nonempty U]
    (hU : U ≤ L.rationalReferenceOpen) (s : Γ(L.sheaf, U)) :
    letI := LineBundle.DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty f hη U
    (L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ U) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s) =
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη (L.genericSectionCoefficient U s) *
        (L.dominantPullbackReferenceCoefficient f hη).val := by
  let := LineBundle.DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty f hη U
  let := LineBundle.DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty f hη L.rationalReferenceOpen
  let r := L.sectionFrame (genericPoint Y) U hU s
  let t := L.sheaf.presheaf.map (homOfLE hU).op L.referenceSection
  have hs := L.section_eq_reference_smul U hU s
  have hp := (congrArg (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U) hs).trans
    (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen_smul f L.sheaf U r t)
  have ht := Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen_restrict f L.sheaf hU L.referenceSection
  have hpre : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ L.rationalReferenceOpen := fun _ h => hU h
  have hc : (L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ U)
      (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U t) = (L.dominantPullbackReferenceCoefficient f hη).val :=
    (congrArg ((L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ U)) ht.symm).trans
      ((L.pullback f).genericSectionCoefficient_restrict hpre _)
  have hb : L.genericSectionCoefficient U s = Y.germToFunctionField U r := by
    rw [L.genericSectionCoefficient_eq_local (genericPoint Y) U hU]
    unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalCoefficient
    rw [L.rationalSectionCoordinate_reference]
    exact div_one _
  have hg := ConcreteCategory.congr_hom (Deformation.FunctionField.BundleCycles.genericFieldMap_germOn f hη U) r
  have hg' : X.germToFunctionField (f ⁻¹ᵁ U) (f.app U r) =
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη (L.genericSectionCoefficient U s) :=
    hg.symm.trans (congrArg (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη) hb.symm)
  calc
    _ = (L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ U)
        (f.app U r • Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U t) :=
      congrArg ((L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ U)) hp
    _ = X.germToFunctionField (f ⁻¹ᵁ U) (f.app U r) *
        (L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ U) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U t) :=
      (L.pullback f).genericSectionCoefficient_smul (f ⁻¹ᵁ U) (f.app U r) _
    _ = _ := congrArg₂ (· * ·) hg' hc

end

/-! # LineBundleCycles: the genuine dominant pullback of every rational line-bundle section -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient_dominant (U : Y.Opens) [Nonempty U] (s : Γ(L.sheaf, U)) :
    letI := LineBundle.DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty f hη U
    (L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ U) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s) =
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη (L.genericSectionCoefficient U s) *
        (L.dominantPullbackReferenceCoefficient f hη).val := by
  let V := L.genericCoefficientDomain U
  let := LineBundle.DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty f hη U
  let := LineBundle.DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty f hη V
  have hVU : V ≤ U := inf_le_left
  have hpre : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U := fun _ h => hVU h
  let t := L.sheaf.presheaf.map (homOfLE hVU).op s
  have hr := Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen_restrict f L.sheaf hVU s
  have hc := (L.pullback f).genericSectionCoefficient_restrict hpre (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s)
  calc
    _ = (L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ V) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf V t) :=
      hc.symm.trans (congrArg ((L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ V)) hr)
    _ = Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη (L.genericSectionCoefficient V t) *
        (L.dominantPullbackReferenceCoefficient f hη).val :=
      L.genericSectionCoefficient_dominant_on_reference f hη V inf_le_right t
    _ = _ := congrArg (fun z => Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη z *
      (L.dominantPullbackReferenceCoefficient f hη).val) (L.genericSectionCoefficient_restrict hVU s)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient_dominantPullback (a : Y.functionFieldˣ)
    (U : Y.Opens) [Nonempty U] (s : Γ(L.sheaf, U)) (hs : L.genericSectionCoefficient U s = a.val) :
    letI := LineBundle.DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty f hη U
    (L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ U) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s) =
      (L.dominantPullbackSectionCoefficient f hη a).val := by
  let := LineBundle.DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty f hη U
  exact (L.genericSectionCoefficient_dominant f hη U s).trans
    (congrArg (fun z => Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη z * (L.dominantPullbackReferenceCoefficient f hη).val) hs)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
