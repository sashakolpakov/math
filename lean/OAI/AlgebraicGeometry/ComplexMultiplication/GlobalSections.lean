import OAI.AlgebraicGeometry.ComplexMultiplication.CMComparisonTo
import OAI.AlgebraicGeometry.Cohomology.GlobalSections
import OAI.AlgebraicTopology.Support.CohomologyFlasqueModel
import OAI.Algebra.Homology.Notation

/-! # Global Sections -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.GlobalSections

noncomputable section

/-! # Hypercohomology computed by global sections of a flasque resolution -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance CMGlobalSections.localInstance1 : HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

/-- For a K-injective complex, the derived definition of hypercohomology agrees with
the cohomology of its global sections. -/
def kInjectiveHypercohomologyGlobalAddEquiv
    (I : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) [I.IsKInjective] (n : ℤ) :
    ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X I n ≃+
      (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt ↧(ComplexPoint.Basic.ComplexSchemePoint X) I).homology n :=
  (show ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X I n ≃+
      ShiftedHom (DerivedCategory.Q.obj (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj I) n from
    { toEquiv := Localization.SmallShiftedHom.equiv
        (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q
      map_add' := ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyEquiv_add X I n }).trans <|
  (show ShiftedHom (DerivedCategory.Q.obj (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj I) n ≃+
      ShiftedHom (DerivedCategory.Q.obj
        (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex ↧(ComplexPoint.Basic.ComplexSchemePoint X)))
        (DerivedCategory.Q.obj I) n from
    Algebra.Homology.DerivedCategoryInjectiveHom.CategoryTheory.isoHomCongrAddEquiv
      (DerivedCategory.Q.mapIso (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X))
      (Iso.refl _)).trans <|
  (Algebra.Homology.DerivedCategoryInjectiveHom.CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass _ I n).trans <|
  (CochainComplex.HomComplex.homologyAddEquiv _ I n).symm.trans
    (HomologicalComplex.homologyMapIso
      (Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections
        ↧(ComplexPoint.Basic.ComplexSchemePoint X) I) n).addCommGroupIsoToAddEquiv

/-- A bounded-below flasque resolution computes hypercohomology by global sections.
The comparison is obtained from its map to an injective resolution, whose global-section
map is a quasi-isomorphism. -/
def flasqueResolutionHypercohomologyGlobalAddEquiv
    (F : ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) [K.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ K) [Mono ι] [QuasiIso ι]
    (hK : ∀ i, (K.X i).IsFlasque) (n : ℤ) :
    ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X K n ≃+
      (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt ↧(ComplexPoint.Basic.ComplexSchemePoint X) K).homology n := by
  let Y : TopCat.{0} := ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  let I := AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex Y F
  let f := AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.resolutionToInjective Y F K ι
  let Γ := AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let e : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X K n ≃+ ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X I n :=
    { toEquiv := Localization.SmallShiftedHom.postcompEquiv f
        (show QuasiIso f from inferInstance)
      map_add' := (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X f n).map_add }
  have hglobal : QuasiIso
      ((Γ.mapHomologicalComplex ℤᵘᵖ).map f) :=
    AlgebraicTopology.Sheaf.FlasqueQuasiIso.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      f 0 0 hK (fun _ ↦ AlgebraicTopology.Sheaf.InjectiveFlasque.TopCat.injective_isFlasque Y _)
  letI := hglobal
  exact e.trans <| (kInjectiveHypercohomologyGlobalAddEquiv X I n).trans
    (asIso (HomologicalComplex.homologyMap
      ((Γ.mapHomologicalComplex ℤᵘᵖ).map f) n)).symm.addCommGroupIsoToAddEquiv

end

end OAI.AlgebraicGeometry.ComplexMultiplication.GlobalSections
