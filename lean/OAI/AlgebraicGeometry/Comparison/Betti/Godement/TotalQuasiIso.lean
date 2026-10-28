import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Bicomplex
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafForget
import OAI.AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor

/-! # Total Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalQuasiIso

noncomputable section

/-! The original Godement total augmentation is a quasi-isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

local instance complexSheafCategoryWithHomology (X : TopCat.{0}) :
    CategoryWithHomology (TopCat.Sheaf (ModuleCat.{0} ℂ) X) :=
  inferInstanceAs (CategoryWithHomology (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)))

variable {X : TopCat.{0}} (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ)

theorem godementTotalAugmentation_forget_quasiIso :
    QuasiIso (((Complex.SheafForget.Flasque.sheafForget X).mapHomologicalComplex (.up ℕ)).map
      (Bicomplex.godementTotalAugmentation K)) := by
  let F := Complex.SheafForget.Flasque.sheafForget X
  have hFA : F.Additive := Complex.SheafForget.Flasque.sheafForgetAdditive X
  have hFH : F.PreservesHomology := Complex.SheafForget.Flasque.sheafForgetPreservesHomology X
  let B := Bicomplex.godementBicomplex X K
  let e := Bicomplex.godementBicomplexAugmentation K
  let he := fun q q' (_ : (ComplexShape.up ℕ).Rel q q') => Bicomplex.godementBicomplexAugmentation_comm K q q'
  let w := Bicomplex.godementBicomplexAugmentation_comp_d K
  have haug (q : ℕ) :
      (ShortComplex.mk (F.map (e q)) (((TotalComplexFunctor.mapBicomplex F B).X q).d 0 1)
        (TotalComplexEdge.mappedHorizontalAugmentation_comp_d F B K e w q)).Exact :=
    (Bicomplex.godementBicomplex_augmentation_exact K q).map F
  have hmono (q : ℕ) : Mono (F.map (e q)) := by
    have hm : Mono (e q) := Bicomplex.godementBicomplex_augmentation_mono K q
    exact F.map_mono (e q)
  have hrows (q p : ℕ) : ((TotalComplexFunctor.mapBicomplex F B).X q).ExactAt (p + 1) := by
    have h : (ShortComplex.mk ((B.X q).d p (p + 1)) ((B.X q).d (p + 1) (p + 2))
        ((B.X q).d_comp_d p (p + 1) (p + 2))).Exact :=
      ((B.X q).exactAt_iff' p (p + 1) (p + 2) (by simp) (by simp)).mp
        (Bicomplex.godementBicomplex_exactAt_succ K q p)
    exact (((TotalComplexFunctor.mapBicomplex F B).X q).exactAt_iff'
      p (p + 1) (p + 2) (by simp) (by simp)).mpr (h.map F)
  have hEdge : QuasiIso (TotalComplexEdge.mappedHorizontalEdge F B K e he w) :=
    Betti.Sheaf.ResolutionTotal.sheafHorizontalEdge_quasiIso (TotalComplexFunctor.mapBicomplex F B)
      ((F.mapHomologicalComplex (.up ℕ)).obj K) (fun q => F.map (e q))
      (TotalComplexEdge.mappedHorizontalAugmentation_comm F B K e he)
      (TotalComplexEdge.mappedHorizontalAugmentation_comp_d F B K e w) haug hmono hrows
  have hIso : IsIso (TotalComplexFunctor.totalComparison F B) :=
    (TotalAdditiveFunctor.totalComparisonIsoOfAdditive F B).isIso_hom
  have h : QuasiIso (TotalComplexEdge.mappedHorizontalEdge F B K e he w ≫
      TotalComplexFunctor.totalComparison F B) := inferInstance
  rw [TotalComplexEdge.mappedHorizontalEdge_comp_totalComparison] at h
  exact h

theorem godementTotalAugmentation_quasiIso : QuasiIso (Bicomplex.godementTotalAugmentation K) := by
  let F := Complex.SheafForget.Flasque.sheafForget X
  have hFA : F.Additive := Complex.SheafForget.Flasque.sheafForgetAdditive X
  have hFH : F.PreservesHomology := Complex.SheafForget.Flasque.sheafForgetPreservesHomology X
  have hF : F.ReflectsIsomorphisms := by
    change (sheafCompose (Opens.grothendieckTopology X)
      Complex.SheafForget.Flasque.scalarForget).ReflectsIsomorphisms
    infer_instance
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (Bicomplex.godementTotalAugmentation K) F).mp (godementTotalAugmentation_forget_quasiIso K)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalQuasiIso
