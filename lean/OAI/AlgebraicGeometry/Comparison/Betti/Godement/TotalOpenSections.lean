import OAI.AlgebraicGeometry.Comparison.Betti.Godement.OpenSections
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalSections
import OAI.AlgebraicGeometry.Comparison.Betti.SectionResolutionTotal

/-! # Total Open Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalOpenSections

noncomputable section

/-! On an open where every original term is acyclic, the original Godement total augmentation is a quasi-isomorphism on sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}} (K : CochainComplex (FlasqueBiproduct.ComplexSheaves X) ℕ) (V : Opens X)

theorem godementOpenAugmentation_exact (F : FlasqueBiproduct.ComplexSheaves X) :
    (ShortComplex.mk ((FlasqueBiproduct.sections V).map ((Functor.stalkFamilyUnit X).app F))
      ((FlasqueBiproduct.sections V).map ((Resolution.godementComplex X F).d 0 1)) (by
        exact ((FlasqueBiproduct.sections V).map_comp _ _).symm.trans
          ((congrArg (FlasqueBiproduct.sections V).map
            (FunctorialResolution.resolution_augmentation_comp (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X) F)).trans
              ((FlasqueBiproduct.sections V).map_zero _ _)))).Exact := by
  let S := ShortComplex.mk ((Functor.stalkFamilyUnit X).app F) ((Resolution.godementComplex X F).d 0 1)
    (FunctorialResolution.resolution_augmentation_comp (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X) F)
  exact ShortComplex.exact_of_f_is_kernel (S.map (FlasqueBiproduct.sections V))
    (KernelFork.mapIsLimit _ (Injective.godementResolutionData F).isKernel (FlasqueBiproduct.sections V))

theorem godementTotalAugmentation_openSections_quasiIso
    (hK : ∀ r q, Subsingleton (Sheaf.H.{0}
      ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat V.isOpenEmbedding).obj
        ((Complex.SheafForget.Flasque.sheafForget X).obj (K.X r))) (q + 1))) :
    QuasiIso (((FlasqueBiproduct.sections V).mapHomologicalComplex (.up ℕ)).map
      (Bicomplex.godementTotalAugmentation K)) := by
  let F := FlasqueBiproduct.sections V
  have hFA : F.Additive := FlasqueBiproduct.sectionsAdditive V
  have hFL : PreservesFiniteLimits F := FlasqueBiproduct.sectionsPreservesFiniteLimits V
  let B := Bicomplex.godementBicomplex X K
  let e := Bicomplex.godementBicomplexAugmentation K
  let he := fun q q' (_ : (ComplexShape.up ℕ).Rel q q') => Bicomplex.godementBicomplexAugmentation_comm K q q'
  let w := Bicomplex.godementBicomplexAugmentation_comp_d K
  have ha (q : ℕ) : (ShortComplex.mk (F.map (e q))
      (((TotalComplexFunctor.mapBicomplex F B).X q).d 0 1)
        (TotalComplexEdge.mappedHorizontalAugmentation_comp_d F B K e w q)).Exact :=
    godementOpenAugmentation_exact V (K.X q)
  have hm (q : ℕ) : Mono (F.map (e q)) := by
    have h : Mono (e q) := Bicomplex.godementBicomplex_augmentation_mono K q
    exact F.map_mono (e q)
  have hr (q p : ℕ) : ((TotalComplexFunctor.mapBicomplex F B).X q).ExactAt (p + 1) :=
    OpenSections.godementComplex_openSections_exactAt_succ (K.X q) V (hK q) p
  have hEdge : QuasiIso (TotalComplexEdge.mappedHorizontalEdge F B K e he w) :=
    SectionResolutionTotal.moduleHorizontalEdge_quasiIso (TotalComplexFunctor.mapBicomplex F B)
      ((F.mapHomologicalComplex (.up ℕ)).obj K) (fun q => F.map (e q))
      (TotalComplexEdge.mappedHorizontalAugmentation_comm F B K e he)
      (TotalComplexEdge.mappedHorizontalAugmentation_comp_d F B K e w) ha hm hr
  have hIso : IsIso (TotalComplexFunctor.totalComparison F B) :=
    (TotalAdditiveFunctor.totalComparisonIsoOfAdditive F B).isIso_hom
  have h : QuasiIso (TotalComplexEdge.mappedHorizontalEdge F B K e he w ≫
      TotalComplexFunctor.totalComparison F B) := inferInstance
  rw [TotalComplexEdge.mappedHorizontalEdge_comp_totalComparison] at h
  exact h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalOpenSections
