import OAI.AlgebraicGeometry.ComplexMultiplication.GlobalNaturality
import OAI.Algebra.Homology.Notation

/-! # Global Naturality Compute -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.GlobalNaturalityCompute

noncomputable section

/-! # The canonical global-section map for flasque resolutions -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance CMGlobalNaturalityCompute.localInstance1 : HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

/-- For a K-injective target, the canonical map is the inverse computed comparison. -/
lemma globalSectionsToHypercohomology_kInjective
    (I : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) [I.IsKInjective] (n : ℤ)
    (x : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt ↧(ComplexPoint.Basic.ComplexSchemePoint X) I).homology n) :
    GlobalNaturality.globalSectionsToHypercohomology X I n x =
      (GlobalSections.kInjectiveHypercohomologyGlobalAddEquiv X I n).symm x := by
  apply (Localization.SmallShiftedHom.equiv
    (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  change (Localization.SmallShiftedHom.equiv _ DerivedCategory.Q)
    (GlobalNaturality.homComplexClassToHypercohomology X I n (GlobalNaturality.globalSectionsToHomComplexClass X I n x)) = _
  rw [GlobalNaturality.homComplexClassToHypercohomology_equiv, HomPostcomp.cohomologyClassToDerived_kInjective]
  dsimp only [GlobalSections.kInjectiveHypercohomologyGlobalAddEquiv, GlobalNaturality.globalSectionsToHomComplexClass,
    AddEquiv.trans_apply, AddEquiv.symm_symm]
  simp [Algebra.Homology.DerivedCategoryInjectiveHom.CategoryTheory.isoHomCongrAddEquiv, Iso.homCongr]

/-- A flasque resolution makes the canonical global-section map an isomorphism.
It is this canonical map whose naturality fixes the scalar actions. -/
theorem globalSectionsToHypercohomology_flasque_bijective
    (F : ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) [K.IsStrictlyGE 0]
    (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ K) [Mono ι] [QuasiIso ι]
    (hK : ∀ i, (K.X i).IsFlasque) (n : ℤ) :
    Function.Bijective (GlobalNaturality.globalSectionsToHypercohomology X K n) := by
  let Y : TopCat.{0} := ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  let I := AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex Y F
  let f := AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.resolutionToInjective Y F K ι
  let Γ := (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
    ℤᵘᵖ
  let e : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X K n ≃ ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X I n :=
    Localization.SmallShiftedHom.postcompEquiv f (show QuasiIso f from inferInstance)
  let : QuasiIso (Γ.map f) :=
    AlgebraicTopology.Sheaf.FlasqueQuasiIso.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      f 0 0 hK (fun _ ↦ AlgebraicTopology.Sheaf.InjectiveFlasque.TopCat.injective_isFlasque Y _)
  have hi : Function.Bijective (GlobalNaturality.globalSectionsToHypercohomology X I n) := by
    have h : ⇑(GlobalNaturality.globalSectionsToHypercohomology X I n) =
        ⇑(GlobalSections.kInjectiveHypercohomologyGlobalAddEquiv X I n).symm :=
      funext (globalSectionsToHypercohomology_kInjective X I n)
    rw [h]
    exact (GlobalSections.kInjectiveHypercohomologyGlobalAddEquiv X I n).symm.bijective
  have hg : Function.Bijective (HomologicalComplex.homologyMap (Γ.map f) n) :=
    (asIso (HomologicalComplex.homologyMap (Γ.map f) n)).addCommGroupIsoToAddEquiv.bijective
  have h : e ∘ GlobalNaturality.globalSectionsToHypercohomology X K n =
      GlobalNaturality.globalSectionsToHypercohomology X I n ∘ HomologicalComplex.homologyMap (Γ.map f) n := by
    funext x
    exact (GlobalNaturality.globalSectionsToHypercohomology_naturality X f n x).symm
  exact (Function.Bijective.of_comp_iff' e.bijective
    (GlobalNaturality.globalSectionsToHypercohomology X K n)).mp (h.symm ▸ hi.comp hg)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.GlobalNaturalityCompute
