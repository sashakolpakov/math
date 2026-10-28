import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison

/-! # Acyclic Cover Total Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicCoverTotalVanishing.IntrinsicCech

noncomputable section

/-! Vanishing in every degree on all intersections of an open cover implies actual sheaf cohomology vanishing in every degree. The cover need not consist of affine opens. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}

theorem restrictedSheaf_sections_subsingleton_of_H_zero
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X)
    (h : Subsingleton (CategoryTheory.Sheaf.H
      ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat V.isOpenEmbedding).obj F) 0)) :
    Subsingleton (F.obj.obj (op V)) := by
  let G := (TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat V.isOpenEmbedding).obj F
  let G' : CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of V)) AddCommGrpCat.{u} := G
  let H : AddCommGrpCat.{u} :=
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology (TopCat.of V)) 0).obj G'
  let e : H ≃+ G'.obj.obj (op ⊤) := CategoryTheory.Sheaf.H.equiv₀ G' isTerminalTop
  have : Subsingleton H := h
  have hs : Subsingleton (G.obj.obj (op ⊤)) :=
    e.symm.injective.subsingleton
  change Subsingleton (F.obj.obj (op (V.isOpenEmbedding.functor.obj ⊤))) at hs
  rwa [Opens.isOpenEmbedding_obj_top V] at hs

theorem cech_term_isZero_of_intersection_sections_zero
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {ι : Type u} (U : ι → Opens X) (p : ℕ)
    (hs : ∀ i : Fin (p + 1) → ι,
      Subsingleton (F.obj.obj (op (∏ᶜ fun k : Fin (p + 1) => U (i k))))) :
    IsZero (((cechComplexFunctor U).obj F.obj).X p) := by
  let (i : Fin (p + 1) → ι) :
      Subsingleton (F.obj.obj (op (∏ᶜ fun k : Fin (p + 1) => U (i k)))) := hs i
  have : Subsingleton (((cechComplexFunctor U).obj F.obj).X p) :=
    (IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U p).injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

theorem sheaf_cohomology_vanish_of_all_intersections
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {ι : Type u} (U : ι → Opens X) (hU : iSup U = ⊤)
    (hH : ∀ (p : ℕ) (i : Fin (p + 1) → ι) (q : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H
        ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat
          (∏ᶜ fun k : Fin (p + 1) => U (i k)).isOpenEmbedding).obj F) q))
    (q : ℕ) : Subsingleton (CategoryTheory.Sheaf.H F q) := by
  have hterm (p : ℕ) : IsZero (((cechComplexFunctor U).obj F.obj).X p) :=
    cech_term_isZero_of_intersection_sections_zero F U p (fun i =>
      restrictedSheaf_sections_subsingleton_of_H_zero F _ (hH p i 0))
  cases q with
  | zero =>
      let a := Cech.GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U
      have : Mono a := Cech.GlobalAugmentationExactness.IntrinsicCech.cechGlobalSectionsAugmentation_mono U F hU
      have : Subsingleton (((cechComplexFunctor U).obj F.obj).X 0) :=
        AddCommGrpCat.subsingleton_of_isZero (hterm 0)
      have : Subsingleton ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).obj F) :=
        ((AddCommGrpCat.mono_iff_injective a).mp inferInstance).subsingleton
      let e := (CategoryTheory.Sheaf.ΓNatIsoSheafSections
        (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).app F
      have : Subsingleton (F.obj.obj (op ⊤)) := e.symm.addCommGroupIsoToAddEquiv.injective.subsingleton
      let F' : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := F
      let H : AddCommGrpCat.{u} :=
        (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 0).obj F'
      let h : H ≃+ F'.obj.obj (op ⊤) := CategoryTheory.Sheaf.H.equiv₀ F' isTerminalTop
      exact h.injective.subsingleton
  | succ n =>
      let C := (cechComplexFunctor U).obj F.obj
      have hC : C.ExactAt (n + 1) :=
        (C.sc (n + 1)).exact_of_isZero_X₂ (hterm (n + 1))
      let e := IntrinsicCech.SheafCohomologyComparison.cechHomologySuccIsoOfAcyclicIntersections U F hU
        (fun p i k => hH p i (k + 1)) n
      exact AddCommGrpCat.subsingleton_of_isZero (hC.isZero_homology.of_iso e.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicCoverTotalVanishing.IntrinsicCech
