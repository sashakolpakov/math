import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FunctionsSheaf

/-! # Global Differential -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.GlobalDifferential.IntegralGlobalDifferential

noncomputable section

/-! When the actual global functions are the base ring, the actual integral first de Rham differential on global sections vanishes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (.of R)))

theorem zeroForms_isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology X.left)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X 0) :=
  (Presheaf.isSheaf_of_iso_iff (LowDegreeSheaves.IntegralLowDegreeSheaves.zeroPresheafIso R X)).mpr
    (FunctionsSheaf.IntegralFunctionsSheaf.isSheaf R X)

theorem zeroForms_unit_isIso (U : X.left.Opens) :
    IsIso ((toSheafify (Opens.grothendieckTopology X.left)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X 0)).app (op U)) := by
  let : IsIso (toSheafify (Opens.grothendieckTopology X.left)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X 0)) := isIso_toSheafify _ (zeroForms_isSheaf R X)
  infer_instance

theorem sectionBaseMap_surjective [IsIso X.hom.appTop] :
    Function.Surjective (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X ⊤) := by
  have hX := (ConcreteCategory.isIso_iff_bijective X.hom.appTop).mp inferInstance
  have hR := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective
  convert hX.surjective.comp hR using 1
  funext r
  simp [AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap, Scheme.Hom.appLE, Scheme.Hom.appTop]
  rfl

theorem presheaf_differential_zero [IsIso X.hom.appTop]
    (ω : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X 0).obj (op ⊤)) :
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X 0).app (op ⊤) ω = 0 := by
  let B := (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op ⊤)
  obtain ⟨a, rfl⟩ := (ZeroForms.IntegralZeroForms.equiv R B).symm.surjective ω
  apply (OneForms.IntegralOneForms.equiv R B).injective
  change OneForms.IntegralOneForms.equiv R B
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R B 0 ((ZeroForms.IntegralZeroForms.equiv R B).symm a)) =
      OneForms.IntegralOneForms.equiv R B 0
  rw [ZeroForms.IntegralZeroForms.first_differential, map_zero]
  obtain ⟨r, hr⟩ := sectionBaseMap_surjective R X a
  change algebraMap R B r = a at hr
  rw [← hr, Derivation.map_algebraMap]

theorem sheaf_differential_zero [IsIso X.hom.appTop]
    (ω : ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X 0).obj.obj (op ⊤)) :
    ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).d 0 1).hom.app (op ⊤) ω = 0 := by
  let : IsIso ((toSheafify (Opens.grothendieckTopology X.left)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X 0)).app (op ⊤)) := zeroForms_unit_isIso R X ⊤
  obtain ⟨a, rfl⟩ := ConcreteCategory.bijective_of_isIso
    ((toSheafify (Opens.grothendieckTopology X.left)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X 0)).app (op ⊤)) |>.surjective ω
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.app (op ⊤))
      (toSheafify_naturality (Opens.grothendieckTopology X.left)
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X 0))) a
  change (toSheafify (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X 1)).app (op ⊤)
    ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X 0).app (op ⊤) a) =
      (sheafifyMap (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X 0)).app (op ⊤)
        ((toSheafify (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X 0)).app (op ⊤) a) at h
  rw [presheaf_differential_zero, map_zero] at h
  convert h.symm using 1 <;> rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.GlobalDifferential.IntegralGlobalDifferential
