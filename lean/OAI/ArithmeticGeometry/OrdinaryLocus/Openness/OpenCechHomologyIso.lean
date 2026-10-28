import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechShortComplex

/-! # Open Cech Homology Iso -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechHomologyIso.Construction

noncomputable section

/-! Identifying the cohomology of the explicit Cech short complex in degrees zero and one. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v

variable {R : Type u} [CommRing R] {X : TopCat.{v}}
    (F : TopCat.Sheaf (ModuleCat.{v} R) X) {ι : Type v} (U : ι → Opens X)

theorem openModuleCechCyclesEquiv_boundaries :
    (LinearMap.range (OpenCechShortComplex.Construction.openModuleCechShortComplex F U).moduleCatToCycles).map
      (OpenCechShortComplex.Construction.openModuleCechCyclesEquiv F U).toLinearMap = LinearMap.range (OpenCechCohomology.Construction.openCechBoundaryMap F U) := by
  ext z
  constructor
  · rintro ⟨w, ⟨x, rfl⟩, hw⟩
    refine ⟨x, ?_⟩
    rw [← hw]
    rfl
  · rintro ⟨x, rfl⟩
    exact ⟨(OpenCechShortComplex.Construction.openModuleCechShortComplex F U).moduleCatToCycles x, ⟨x, rfl⟩, rfl⟩

def openModuleCechQuotientEquiv :
    (LinearMap.ker (OpenCechShortComplex.Construction.openModuleCechD1 F U) ⧸
      LinearMap.range (OpenCechShortComplex.Construction.openModuleCechShortComplex F U).moduleCatToCycles) ≃ₗ[R] OpenCechCohomology.Construction.OpenCechH1 F U :=
  Submodule.Quotient.equiv _ _ (OpenCechShortComplex.Construction.openModuleCechCyclesEquiv F U)
    (openModuleCechCyclesEquiv_boundaries F U)

def openModuleCechHomologyIso :
    (OpenCechShortComplex.Construction.openModuleCechShortComplex F U).homology ≅ ModuleCat.of R (OpenCechCohomology.Construction.OpenCechH1 F U) :=
  (OpenCechShortComplex.Construction.openModuleCechShortComplex F U).moduleCatHomologyIso ≪≫
    (openModuleCechQuotientEquiv F U).toModuleIso

def openModuleCechGlobalSectionsEquiv (hU : iSup U = ⊤) :
    F.obj.obj (op ⊤) ≃ₗ[R] LinearMap.ker (OpenCechShortComplex.Construction.openModuleCechShortComplex F U).f.hom :=
  LinearEquiv.ofBijective
    ((OpenCechDegreeZero.Construction.openModuleCechUnit F U).codRestrict _ (fun s =>
      (OpenCechDegreeZero.Construction.openModuleCech_exact_degreeZero F U hU (OpenCechDegreeZero.Construction.openModuleCechUnit F U s)).mpr ⟨s, rfl⟩))
    ⟨fun x y h => OpenCechDegreeZero.Construction.openModuleCechUnit_injective F U hU (congrArg Subtype.val h), by
      intro x
      obtain ⟨s, hs, _⟩ := OpenCechDegreeZero.Construction.openModuleCech_sections_glue F U hU x.val x.property
      exact ⟨s, Subtype.ext hs⟩⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechHomologyIso.Construction
