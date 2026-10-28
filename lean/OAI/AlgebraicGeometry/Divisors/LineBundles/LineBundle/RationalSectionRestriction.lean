import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalSectionNeighborhood
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.LocalGeneratorPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportNaturality

/-! # Rational Section Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: restrict the actual rational section to a prime support through a genuine unit neighborhood -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X} {a : X.functionFieldˣ} {x : X}
    (D : L.RationalSectionUnitNeighborhood a x)

instance Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.RationalSectionUnitNeighborhood.supportPreimage_nonempty :
    Nonempty ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) ⁻¹ᵁ D.openSet) := by
  refine ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)), ?_⟩⟩
  change CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) (genericPoint _) ∈ D.openSet
  rw [Point.SupportNaturality.BundleCycles.pointSupport_genericPoint]
  exact D.point_mem

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.RationalSectionUnitNeighborhood.restrictionCoefficient : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionFieldˣ :=
  LineBundle.LocalGeneratorPullback.Cycles.lineBundleLocalGeneratorPullbackCoefficient (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) L
    D.openSet D.trivialization D.localSection (by rw [D.trivialization_generator]; exact isUnit_one)

omit [AlgebraicGeometry.IsNoetherian X] in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.RationalSectionUnitNeighborhood.restrictionCoefficient_apply : D.restrictionCoefficient.val =
    (L.pullback (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x))).genericSectionCoefficient
      ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) ⁻¹ᵁ D.openSet)
      (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) L.sheaf D.openSet D.localSection) := rfl

omit [AlgebraicGeometry.IsNoetherian X] in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.RationalSectionUnitNeighborhood.restrictionCoefficient_independent (E : L.RationalSectionUnitNeighborhood a x) :
    D.restrictionCoefficient = E.restrictionCoefficient := by
  let i := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)
  let M := L.pullback i
  let V : X.Opens := D.openSet ⊓ E.openSet
  let S := i ⁻¹ᵁ V
  let : Nonempty S := by
    refine ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)), ?_⟩⟩
    change i (genericPoint _) ∈ V
    rw [Point.SupportNaturality.BundleCycles.pointSupport_genericPoint]
    exact ⟨D.point_mem, E.point_mem⟩
  have hSD : S ≤ i ⁻¹ᵁ D.openSet := fun _ h => h.1
  have hSE : S ≤ i ⁻¹ᵁ E.openSet := fun _ h => h.2
  have hsections := L.localSections_agree_on_overlap x x D.openSet E.openSet D.subordinate E.subordinate
    D.localSection E.localSection (D.localSection_coefficient.trans E.localSection_coefficient.symm)
  have hD := Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen_restrict i L.sheaf (show V ≤ D.openSet from inf_le_left) D.localSection
  have hE := Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen_restrict i L.sheaf (show V ≤ E.openSet from inf_le_right) E.localSection
  have hPull := hD.trans ((congrArg (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen i L.sheaf V) hsections).trans hE.symm)
  apply Units.ext
  change M.genericSectionCoefficient (i ⁻¹ᵁ D.openSet) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen i L.sheaf D.openSet D.localSection) =
    M.genericSectionCoefficient (i ⁻¹ᵁ E.openSet) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen i L.sheaf E.openSet E.localSection)
  calc
    _ = M.genericSectionCoefficient S
        (M.sheaf.presheaf.map (homOfLE hSD).op (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen i L.sheaf D.openSet D.localSection)) :=
      (M.genericSectionCoefficient_restrict hSD _).symm
    _ = M.genericSectionCoefficient S
        (M.sheaf.presheaf.map (homOfLE hSE).op (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen i L.sheaf E.openSet E.localSection)) :=
      congrArg (M.genericSectionCoefficient S) hPull
    _ = _ := M.genericSectionCoefficient_restrict hSE _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
