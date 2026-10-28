import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PuncturedDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.LaurentNaturality
import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DivisorPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage

/-! # Support Extension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.SupportExtension.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: principal divisors on every actual closed support extend to principal divisors -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} (I : X.IdealSheafData)

theorem supportPuncturedCycleExtension_toAmbient (P : X.IdealSheafData) (z : P.subscheme →₀ ℚ) :
    Finsupp.mapDomain (Support.LaurentChart.BundleCycles.supportPuncturedMap I P) (Support.PuncturedDivisor.BundleCycles.supportPuncturedCycleExtension I P z) =
      DivisorPullback.BundleCycles.puncturedCycleExtension I (Finsupp.mapDomain P.subschemeι z) := by
  change Finsupp.mapDomain (Support.LaurentChart.BundleCycles.supportPuncturedMap I P) (Finsupp.mapDomain (Support.PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint I P) z) =
    Finsupp.mapDomain (DeformationFlat.BundleCycles.puncturedFiberGenericPoint I) (Finsupp.mapDomain P.subschemeι z)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  exact congrArg (fun h => Finsupp.mapDomain h z)
    (funext (Support.LaurentNaturality.BundleCycles.supportPuncturedGenericPoint_toAmbient I P))

def puncturedExtendedSupport (W : IrreducibleCloseds X) : IrreducibleCloseds (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I) :=
  CycleClass.Geometric.StratumClosure.integralImageClosure (Support.LaurentChart.BundleCycles.supportPuncturedMap I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W))

theorem puncturedExtendedSupport_genericPoint (W : IrreducibleCloseds X) :
    irreducibleSetEquivPoints (puncturedExtendedSupport I W) =
      DeformationFlat.BundleCycles.puncturedFiberGenericPoint I (irreducibleSetEquivPoints W) := by
  exact (Integral.ClosedImage.BundleCycles.integralClosedImage_genericPoint (Support.LaurentChart.BundleCycles.supportPuncturedMap I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W))).trans
    ((congrArg (Support.LaurentChart.BundleCycles.supportPuncturedMap I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W))
      (Support.PuncturedFunctionField.BundleCycles.supportPuncturedGenericPoint_generic I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W)).symm).trans
        ((Support.LaurentNaturality.BundleCycles.supportPuncturedGenericPoint_toAmbient I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W) _).trans
          (congrArg (DeformationFlat.BundleCycles.puncturedFiberGenericPoint I) (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W))))

theorem puncturedExtendedSupport_eq_pointClosure (W : IrreducibleCloseds X) :
    puncturedExtendedSupport I W =
      irreducibleSetEquivPoints.symm (DeformationFlat.BundleCycles.puncturedFiberGenericPoint I (irreducibleSetEquivPoints W)) :=
  irreducibleSetEquivPoints.injective ((puncturedExtendedSupport_genericPoint I W).trans
    (irreducibleSetEquivPoints.apply_symm_apply _).symm)

variable [AlgebraicGeometry.IsNoetherian X]

def puncturedExtendedRationalFunction (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (puncturedExtendedSupport I W)).functionField :=
  Integral.ClosedImage.BundleCycles.integralClosedImageFunction (Support.LaurentChart.BundleCycles.supportPuncturedMap I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W))
    (Support.PuncturedFunctionField.BundleCycles.supportPuncturedFunctionFieldMap I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W) g)

omit [AlgebraicGeometry.IsNoetherian X] in
theorem puncturedExtendedRationalFunction_ne_zero (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    puncturedExtendedRationalFunction I W g ≠ 0 :=
  Integral.ClosedImage.BundleCycles.integralClosedImageFunction_ne_zero (Support.LaurentChart.BundleCycles.supportPuncturedMap I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W)) _
    ((map_ne_zero_iff _ (Support.PuncturedFunctionField.BundleCycles.supportPuncturedFunctionFieldMap I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W)).hom.injective).mpr hg)

theorem puncturedCycleExtension_principal (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    DivisorPullback.BundleCycles.puncturedCycleExtension I (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (puncturedExtendedSupport I W) (puncturedExtendedRationalFunction I W g) := by
  let P := CycleClass.Geometric.GenericPoint.reducedSupportIdeal W
  have he : Finsupp.mapDomain P.subschemeι (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor P.subscheme g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g :=
    (Finsupp.embDomain_eq_mapDomain
      ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W, (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective⟩
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g)).symm
  exact (congrArg (DivisorPullback.BundleCycles.puncturedCycleExtension I) he.symm).trans
    ((supportPuncturedCycleExtension_toAmbient I P _).symm.trans
      ((congrArg (Finsupp.mapDomain (Support.LaurentChart.BundleCycles.supportPuncturedMap I P))
        (Support.PuncturedDivisor.BundleCycles.supportPuncturedPrincipalDivisor_pullback I P g hg).symm).trans
          (Integral.ClosedImage.BundleCycles.integralClosedImage_principalDivisor (Support.LaurentChart.BundleCycles.supportPuncturedMap I P) _)))

end

section

/-! # LineBundleCycles: the global punctured cycle extension raises the actual support dimension by one -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} (I : X.IdealSheafData) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem puncturedExtendedSupport_dimension (W : IrreducibleCloseds X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (puncturedExtendedSupport I W) (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f + 1 := by
  let P := CycleClass.Geometric.GenericPoint.reducedSupportIdeal W
  have hc : Support.LaurentChart.BundleCycles.supportPuncturedMap I P ≫ (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) =
      Support.LaurentChart.BundleCycles.supportPuncturedProjection I P ≫ (P.subschemeι ≫ f) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ f) (Support.LaurentChart.BundleCycles.supportPuncturedMap_toBase I P)).trans (Category.assoc _ _ _))
  exact (CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure (Support.LaurentChart.BundleCycles.supportPuncturedMap I P)
    (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f)).symm.trans
      ((congrArg (fun k => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension k) hc).trans
        (Support.PuncturedFunctionField.BundleCycles.supportPunctured_dimension I P (P.subschemeι ≫ f)))

theorem puncturedFiberGenericPoint_dimension (x : X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (DeformationFlat.BundleCycles.puncturedFiberGenericPoint I x))
        (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + 1 := by
  have he := puncturedExtendedSupport_eq_pointClosure I (irreducibleSetEquivPoints.symm x)
  rw [irreducibleSetEquivPoints.apply_symm_apply] at he
  exact (congrArg (fun W => Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f)) he).symm.trans
    (puncturedExtendedSupport_dimension I f _)

def puncturedDimensionPointMap (d : ℕ) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d → Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) (d + 1) :=
  fun x => ⟨DeformationFlat.BundleCycles.puncturedFiberGenericPoint I x.1,
    (puncturedFiberGenericPoint_dimension I f x.1).trans (congrArg (fun n => n + 1) x.2)⟩

def puncturedGradedCycleExtension (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ]
      (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) (d + 1) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (puncturedDimensionPointMap I f d)

theorem puncturedGradedCycleExtension_forget (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) (d + 1)
        (puncturedGradedCycleExtension I f d z) =
      DivisorPullback.BundleCycles.puncturedCycleExtension I (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) := by
  change Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) (d + 1))
      (Finsupp.mapDomain (puncturedDimensionPointMap I f d) z) =
    Finsupp.mapDomain (DeformationFlat.BundleCycles.puncturedFiberGenericPoint I) (Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) z)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

end

/-! # LineBundleCycles: genuine Chow pullback from the original scheme to its punctured deformation -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

instance puncturedDeformationProjection_finiteType : LocallyOfFiniteType (DeformationCharts.BundleCycles.puncturedDeformationProjection I) :=
  inferInstanceAs (LocallyOfFiniteType (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I ≫ Global.Deformation.BundleCycles.globalDeformationProjection I))

theorem puncturedGradedCycleExtension_principal (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    puncturedGradedCycleExtension I f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g) =
      Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) (d + 1)
        (puncturedExtendedSupport I W) (puncturedExtendedRationalFunction I W g) := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) (d + 1)
  rw [puncturedGradedCycleExtension_forget, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d W hW,
    puncturedCycleExtension_principal I W g hg,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) (d + 1)
      (puncturedExtendedSupport I W) ((puncturedExtendedSupport_dimension I f W).trans
        (congrArg (fun n => n + 1) hW))]

theorem puncturedGradedCycleExtension_isPrincipal (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ)
    (hz : DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ f d z) :
    DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) (d + 1)
      (puncturedGradedCycleExtension I f d z) := by
  obtain ⟨W, hW, g, hg, rfl⟩ := hz
  exact ⟨puncturedExtendedSupport I W,
    (puncturedExtendedSupport_dimension I f W).trans (congrArg (fun n => n + 1) hW),
    puncturedExtendedRationalFunction I W g, puncturedExtendedRationalFunction_ne_zero I W g hg,
    puncturedGradedCycleExtension_principal I f d W hW g hg⟩

theorem puncturedGradedCycleExtension_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) (d + 1)).comap
        (puncturedGradedCycleExtension I f d) := by
  apply Submodule.span_le.mpr
  intro z hz
  exact Submodule.subset_span (puncturedGradedCycleExtension_isPrincipal I f d z hz)

def puncturedChowExtension (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) (d + 1) :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).mapQ
    (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) (d + 1))
    (puncturedGradedCycleExtension I f d) (puncturedGradedCycleExtension_relations I f d)

@[simp]
theorem puncturedChowExtension_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    puncturedChowExtension I f d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) (d + 1)
        (puncturedGradedCycleExtension I f d z) := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.SupportExtension.BundleCycles
