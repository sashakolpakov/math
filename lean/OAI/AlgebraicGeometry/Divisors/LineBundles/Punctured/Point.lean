import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.ProductCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecializationComparison

/-! # Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.Point.BundleCycles

noncomputable section

/-! The full punctured specialization input is the actual Laurent fiber generic-point extension in the literal deformation grading. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem dimensionCycleTransport_single {S : Scheme.{0}} {f g : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    (h : f = g) (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d) (y : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint g d)
    (hxy : x.val = y.val) (r : ℚ) :
    DimensionChow.BundleCycles.dimensionCycleTransport h d (Finsupp.single x r) = Finsupp.single y r := by
  subst g
  have he : x = y := Subtype.ext hxy
  subst y
  rfl

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [AlgebraicGeometry.IsNoetherian X.left] [LocallyOfFiniteType X.hom]
  (I : X.left.IdealSheafData) (d : ℕ)

def puncturedInputPoint (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (ProductCharts.BundleCycles.puncturedDeformationOver X I).hom (d + 1) :=
  ⟨DeformationFlat.BundleCycles.puncturedFiberGenericPoint I x.val, by
    have h := SupportExtension.BundleCycles.puncturedFiberGenericPoint_dimension I X.hom x.val
    rw [Global.ChowSpecialization.BundleCycles.puncturedStructureMap_eq I X.hom] at h
    exact h.trans (congrArg (fun n => n + 1) x.property)⟩

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem puncturedSpecializationCycleInput_single (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) (r : ℚ) :
    Global.SpecializationComparison.BundleCycles.puncturedSpecializationCycleInput I X.hom d (Finsupp.single x r) =
      Finsupp.single (puncturedInputPoint X I d x) r := by
  change DimensionChow.BundleCycles.dimensionCycleTransport (Global.ChowSpecialization.BundleCycles.puncturedStructureMap_eq I X.hom) (d + 1)
    (SupportExtension.BundleCycles.puncturedGradedCycleExtension I X.hom d (Finsupp.single x r)) = _
  have h : SupportExtension.BundleCycles.puncturedGradedCycleExtension I X.hom d (Finsupp.single x r) =
      Finsupp.single (SupportExtension.BundleCycles.puncturedDimensionPointMap I X.hom d x) r := Finsupp.mapDomain_single
  rw [h]
  exact dimensionCycleTransport_single (Global.ChowSpecialization.BundleCycles.puncturedStructureMap_eq I X.hom) (d + 1)
    (SupportExtension.BundleCycles.puncturedDimensionPointMap I X.hom d x) (puncturedInputPoint X I d x) rfl r

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem puncturedInputPoint_support (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) :
    SupportExtension.BundleCycles.puncturedExtendedSupport I (irreducibleSetEquivPoints.symm x.val) =
      irreducibleSetEquivPoints.symm (puncturedInputPoint X I d x).val := by
  change SupportExtension.BundleCycles.puncturedExtendedSupport I (irreducibleSetEquivPoints.symm x.val) =
    irreducibleSetEquivPoints.symm (DeformationFlat.BundleCycles.puncturedFiberGenericPoint I x.val)
  simpa only [OrderIso.apply_symm_apply] using
    SupportExtension.BundleCycles.puncturedExtendedSupport_eq_pointClosure I (irreducibleSetEquivPoints.symm x.val)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.Point.BundleCycles
