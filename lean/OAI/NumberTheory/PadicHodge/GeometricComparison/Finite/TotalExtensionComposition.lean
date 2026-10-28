import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexExtensionHom
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.Hypercohomology

/-! # Total Extension Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalExtensionComposition.FiniteTotalExtensionComposition

noncomputable section

/-! The actual finite total comparison in integer degrees respects composition of additive coefficient functors. -/

open _root_.CategoryTheory Limits _root_.HomologicalComplex₂

theorem four_factors {C : Type*} [Category* C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F)
    (p : B ⟶ G) (q : G ⟶ E) (t : A ⟶ G) (z : G ⟶ F)
    (h : b ≫ c = p ≫ q) (h₁ : a ≫ p = t) (h₂ : q ≫ d = z) :
    (a ≫ b) ≫ (c ≫ d) = t ≫ z := by
  calc
    (a ≫ b) ≫ (c ≫ d) = a ≫ (b ≫ c) ≫ d := by simp only [Category.assoc]
    _ = a ≫ (p ≫ q) ≫ d := by rw [h]
    _ = (a ≫ p) ≫ (q ≫ d) := by simp only [Category.assoc]
    _ = t ≫ z := by rw [h₁, h₂]

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  [HasFiniteCoproducts C] [HasFiniteCoproducts D] [HasFiniteCoproducts E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

local instance (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance (K : HomologicalComplex₂ D (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance (K : HomologicalComplex₂ E (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

theorem hom (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) :
    (TotalIso.FiniteTotalExtension.iso G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K)).hom ≫
        (G.mapHomologicalComplex (.up ℤ)).map (TotalIso.FiniteTotalExtension.iso F K).hom =
      (TotalIso.FiniteTotalExtension.iso (F ⋙ G) K).hom := by
  let eF := AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K
  let eG := AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K)
  let eFG := AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso (F ⋙ G) K
  let bF := AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat (K.total (.up ℕ))
  let bG := AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso G ComplexShape.embeddingUpNat
    ((AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).total (.up ℕ))
  let bGF := AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso G ComplexShape.embeddingUpNat
    ((F.mapHomologicalComplex (.up ℕ)).obj (K.total (.up ℕ)))
  let bFG := AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso (F ⋙ G) ComplexShape.embeddingUpNat (K.total (.up ℕ))
  let GN := G.mapHomologicalComplex (.up ℕ)
  let GZ := G.mapHomologicalComplex (.up ℤ)
  let U := ComplexShape.embeddingUpNat.extendFunctor E
  let UD := ComplexShape.embeddingUpNat.extendFunctor D
  have hs : bG.inv ≫ GZ.map (UD.map eF.hom) = U.map (GN.map eF.hom) ≫ bGF.inv :=
    (Section.Hypercohomology.SectionHypercohomology.inverse_square bG bGF _ _
      (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso_naturality G ComplexShape.embeddingUpNat eF.hom)).symm
  have ht : U.map eG.hom ≫ U.map (GN.map eF.hom) = U.map eFG.hom :=
    (U.map_comp _ _).symm.trans (congrArg U.map (TotalIso.FiniteTotalComposition.hom F G K))
  have he : GZ.mapIso bF ≪≫ bGF = bFG :=
    Iso.ext (ComplexExtensionHom.ComplexExtensionComposition.hom F G ComplexShape.embeddingUpNat (K.total (.up ℕ)))
  have hb : bGF.inv ≫ GZ.map bF.inv = bFG.inv := congrArg Iso.inv he
  exact (congrArg (fun k => (TotalIso.FiniteTotalExtension.iso G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K)).hom ≫ k)
    (GZ.map_comp (UD.map eF.hom) bF.inv)).trans
      (four_factors (U.map eG.hom) bG.inv (GZ.map (UD.map eF.hom)) (GZ.map bF.inv)
        (U.map (GN.map eF.hom)) bGF.inv (U.map eFG.hom) bFG.inv hs ht hb)

theorem hom_inverse (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) :
    (TotalIso.FiniteTotalExtension.iso G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K)).hom =
      (TotalIso.FiniteTotalExtension.iso (F ⋙ G) K).hom ≫
        (G.mapHomologicalComplex (.up ℤ)).map (TotalIso.FiniteTotalExtension.iso F K).inv := by
  let e := (G.mapHomologicalComplex (.up ℤ)).mapIso (TotalIso.FiniteTotalExtension.iso F K)
  exact (e.comp_inv_eq.mpr (FiniteTotalExtensionComposition.hom F G K).symm).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalExtensionComposition.FiniteTotalExtensionComposition
