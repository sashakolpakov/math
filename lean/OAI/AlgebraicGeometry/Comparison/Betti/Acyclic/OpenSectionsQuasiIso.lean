import OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalOpenSections

/-! # Open Sections Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.OpenSectionsQuasiIso.Godement

noncomputable section

/-! Actual open sections preserve a quasi-isomorphism between nonnegative complexes whose terms are acyclic on that open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

local instance acyclicOpenSectionsCategoryWithHomology (X : TopCat.{0}) :
    CategoryWithHomology (FlasqueBiproduct.ComplexSheaves X) :=
  inferInstanceAs (CategoryWithHomology (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)))

variable {X : TopCat.{0}} {K L : CochainComplex (FlasqueBiproduct.ComplexSheaves X) ℕ}
  (f : K ⟶ L) (hf : QuasiIso f) (V : Opens X)

include hf

theorem acyclic_openSections_quasiIso
    (hK : ∀ r q, Subsingleton (Sheaf.H.{0}
      ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat V.isOpenEmbedding).obj
        ((Complex.SheafForget.Flasque.sheafForget X).obj (K.X r))) (q + 1)))
    (hL : ∀ r q, Subsingleton (Sheaf.H.{0}
      ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat V.isOpenEmbedding).obj
        ((Complex.SheafForget.Flasque.sheafForget X).obj (L.X r))) (q + 1))) :
    QuasiIso (((FlasqueBiproduct.sections V).mapHomologicalComplex (.up ℕ)).map f) := by
  let H := (FlasqueBiproduct.sections V).mapHomologicalComplex (.up ℕ)
  have heK : QuasiIso (H.map (Godement.Bicomplex.godementTotalAugmentation K)) :=
    Godement.TotalOpenSections.godementTotalAugmentation_openSections_quasiIso K V hK
  have heL : QuasiIso (H.map (Godement.Bicomplex.godementTotalAugmentation L)) :=
    Godement.TotalOpenSections.godementTotalAugmentation_openSections_quasiIso L V hL
  have hG : QuasiIso (H.map (Godement.TotalNaturality.godementTotalMap f)) := Godement.TotalSections.godementTotalMap_sections_quasiIso f hf V
  have hn : H.map (Godement.Bicomplex.godementTotalAugmentation K) ≫ H.map (Godement.TotalNaturality.godementTotalMap f) =
      H.map f ≫ H.map (Godement.Bicomplex.godementTotalAugmentation L) :=
    (H.map_comp _ _).symm.trans
      ((congrArg H.map (Godement.TotalNaturality.godementTotalAugmentation_naturality f)).trans (H.map_comp _ _))
  have hc : QuasiIso (H.map f ≫ H.map (Godement.Bicomplex.godementTotalAugmentation L)) := by
    rw [← hn]
    exact quasiIso_comp _ _ (hφ := heK) (hφ' := hG)
  exact quasiIso_of_comp_right (H.map f) (H.map (Godement.Bicomplex.godementTotalAugmentation L))
    (hφ := heL) (hφφ' := hc)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.OpenSectionsQuasiIso.Godement
