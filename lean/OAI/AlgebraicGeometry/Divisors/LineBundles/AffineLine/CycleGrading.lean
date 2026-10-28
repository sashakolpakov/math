import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Dimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Support
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization

/-! # Cycle Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.CycleGrading.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: the actual relative affine line increases every integral support dimension by one -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {k : Type} [Field k] (X : Scheme.{0})

theorem affineLine_dimension [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Charts.BundleCycles.affineLineProjection X ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f + 1 := by
  let x : X := Classical.choice inferInstance
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let V : X.affineOpens := ⟨U, hU⟩
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : IsDomain Γ(X, U) := inferInstance
  have hbase : Charts.BundleCycles.affineLinePolynomialChart X V ≫ Charts.BundleCycles.affineLineProjection X =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Polynomial Γ(X, U)))) ≫ hU.fromSpec :=
    Charts.BundleCycles.affineLinePolynomialChart_toBase X V
  exact @LineBundles.Polynomial.Dimension.BundleCycles.polynomial_dimension_of_chart k _ Γ(X, U) _ _ X (Charts.BundleCycles.affineLine X) _ _
    hU.fromSpec (IsAffineOpen.isOpenImmersion_fromSpec hU)
    (Charts.BundleCycles.affineLinePolynomialChart X V) (Charts.BundleCycles.affineLinePolynomialChart_isOpenImmersion X V)
    (Charts.BundleCycles.affineLineProjection X) hbase f inferInstance

theorem affineLineExtendedSupport_dimension (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (W : IrreducibleCloseds X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Support.BundleCycles.affineLineExtendedSupport X W) (Charts.BundleCycles.affineLineProjection X ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f + 1 := by
  have hc : Support.BundleCycles.affineLineSupportMap X W ≫ (Charts.BundleCycles.affineLineProjection X ≫ f) =
      Charts.BundleCycles.affineLineProjection (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ f) (Support.BundleCycles.affineLineSupport_isPullback X W).w.symm).trans (Category.assoc _ _ _))
  exact (CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure (Support.BundleCycles.affineLineSupportMap X W)
    (Charts.BundleCycles.affineLineProjection X ≫ f)).symm.trans
      ((congrArg (fun q => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension q) hc).trans
        (affineLine_dimension (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f)))

end

/-! # LineBundleCycles: actual dimension-graded cycle pullback to the relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem affineLineFiberGenericPoint_dimension (x : X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x))
        (Charts.BundleCycles.affineLineProjection X ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + 1 := by
  have he := Support.BundleCycles.affineLineExtendedSupport_eq_pointClosure X (irreducibleSetEquivPoints.symm x)
  rw [irreducibleSetEquivPoints.apply_symm_apply] at he
  exact (congrArg (fun W => Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (Charts.BundleCycles.affineLineProjection X ≫ f)) he).symm.trans
    (affineLineExtendedSupport_dimension X f _)

def affineLineDimensionPointMap (d : ℕ) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d → Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) :=
  fun x => ⟨Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x.1,
    (affineLineFiberGenericPoint_dimension X f x.1).trans (congrArg (fun n => n + 1) x.2)⟩

def affineLineGradedCycleExtension (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ]
      (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (affineLineDimensionPointMap X f d)

theorem affineLineGradedCycleExtension_forget (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
        (affineLineGradedCycleExtension X f d z) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) := by
  change Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1))
      (Finsupp.mapDomain (affineLineDimensionPointMap X f d) z) =
    Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) (Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) z)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.CycleGrading.BundleCycles
