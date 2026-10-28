import OAI.AlgebraicGeometry.Comparison.Betti.Cech.RowSectionsProduct
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveTotalColumn

/-! # Row -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.Row

noncomputable section

/-! Quasi-isomorphisms on all tuple-intersection sections give a quasi-isomorphism of the actual Čech totals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex₂

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)
  {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ} (f : K ⟶ L)

def additiveSheafSectionCechBicomplexMap :
    FlasqueCechTotal.additiveSheafSectionCechBicomplex U K ⟶ FlasqueCechTotal.additiveSheafSectionCechBicomplex U L :=
  ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).mapHomologicalComplex (.up ℕ)).map f

def cechRowMap (p : ℕ) : (FlasqueCechTotal.additiveSheafSectionCechBicomplex U K).flip.X p ⟶
    (FlasqueCechTotal.additiveSheafSectionCechBicomplex U L).flip.X p :=
  ((flipFunctor AddCommGrpCat (.up ℕ) (.up ℕ)).map
    (additiveSheafSectionCechBicomplexMap U f)).f p

def cechTupleSectionsMap (p : ℕ) (t : Fin (p + 1) → ι) :
    RowSectionsProduct.cechTupleSectionsComplex U K p t ⟶ RowSectionsProduct.cechTupleSectionsComplex U L p t :=
  ((RowSectionsProduct.additiveOpenSectionsFunctor (∏ᶜ fun k : Fin (p + 1) => U (t k))).mapHomologicalComplex (.up ℕ)).map f

theorem cechRowSectionProjection_naturality (p : ℕ) (t : Fin (p + 1) → ι) :
    cechRowMap U f p ≫ RowSectionsProduct.cechRowSectionProjection U L p t =
      RowSectionsProduct.cechRowSectionProjection U K p t ≫ cechTupleSectionsMap U f p t := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact CategoryTheory.Limits.Pi.map_π
    (fun s : Fin (p + 1) → ι => (f.f n).hom.app (op (∏ᶜ fun k => U (s k)))) t

theorem cechRowSectionsProductIso_naturality (p : ℕ) :
    cechRowMap U f p ≫ (RowSectionsProduct.cechRowSectionsProductIso U L p).hom =
      (RowSectionsProduct.cechRowSectionsProductIso U K p).hom ≫ CategoryTheory.Limits.Pi.map (cechTupleSectionsMap U f p) := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro t
  erw [Category.assoc, RowSectionsProduct.cechRowSectionsProductIso_hom_π, Category.assoc,
    CategoryTheory.Limits.Pi.map_π, ← Category.assoc, RowSectionsProduct.cechRowSectionsProductIso_hom_π]
  exact cechRowSectionProjection_naturality U f p t

theorem cechRowMap_quasiIso [Finite ι] (p : ℕ)
    (hf : ∀ t : Fin (p + 1) → ι, QuasiIso (cechTupleSectionsMap U f p t)) :
    QuasiIso (cechRowMap U f p) := by
  have hp : QuasiIso (CategoryTheory.Limits.Pi.map (cechTupleSectionsMap U f p)) :=
    Betti.Finite.ProductQuasiIso.Total.finiteProduct_quasiIso (cechTupleSectionsMap U f p) hf
  have hK : QuasiIso (RowSectionsProduct.cechRowSectionsProductIso U K p).hom := quasiIso_of_isIso _
  have hL : QuasiIso (RowSectionsProduct.cechRowSectionsProductIso U L p).hom := quasiIso_of_isIso _
  have hc : QuasiIso (cechRowMap U f p ≫ (RowSectionsProduct.cechRowSectionsProductIso U L p).hom) := by
    rw [cechRowSectionsProductIso_naturality]
    exact quasiIso_comp _ _ (hφ := hK) (hφ' := hp)
  exact quasiIso_of_comp_right (cechRowMap U f p) (RowSectionsProduct.cechRowSectionsProductIso U L p).hom
    (hφ := hL) (hφφ' := hc)

theorem cechTotalMap_quasiIso_of_intersectionSections [Finite ι]
    (hf : ∀ p (t : Fin (p + 1) → ι), QuasiIso (cechTupleSectionsMap U f p t)) :
    QuasiIso (total.map (additiveSheafSectionCechBicomplexMap U f) (.up ℕ)) :=
  AdditiveTotalColumn.additive_total_map_quasiIso_of_rows (additiveSheafSectionCechBicomplexMap U f)
    (fun p => cechRowMap_quasiIso U f p (hf p))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.Row
