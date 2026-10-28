/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafDerivedGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedComplexExtensionIso

/-! # Mapped Complex Extension Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedComplexExtensionNaturality.DerivedSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.CategoryTheory.Abelian.Ext
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]
variable {Z F : C}

lemma mapExtendIso_hom_f (K : CochainComplex C ℕ) (n : ℤ) :
    (MappedComplexExtensionIso.DerivedSections.mapExtendIso (G := G) K).hom.f n = (MappedComplexExtension.DerivedSections.mapExtendXIso (G := G) K n).hom :=
  rfl

lemma mapExtendIso_naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    (G.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) ≫
          (MappedComplexExtensionIso.DerivedSections.mapExtendIso L).hom =
      (MappedComplexExtensionIso.DerivedSections.mapExtendIso K).hom ≫
        HomologicalComplex.extendMap
          ((G.mapHomologicalComplex (.up ℕ)).map f) ComplexShape.embeddingUpNat := by
  classical
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    mapExtendIso_hom_f (G := G), mapExtendIso_hom_f (G := G),
    Functor.mapHomologicalComplex_map_f]
  by_cases h : ∃ k, ComplexShape.embeddingUpNat.f k = n
  · obtain ⟨k, hk⟩ := h
    have hk' : (k : ℤ) = n := (ComplexShape.embeddingUpNat_f k).symm.trans hk
    clear hk
    subst n
    rw [HomologicalComplex.extendMap_f f ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat_f k),
      HomologicalComplex.extendMap_f
        ((G.mapHomologicalComplex (.up ℕ)).map f)
        ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)]
    rw [MappedComplexExtension.DerivedSections.mapExtendXIso_natCast (G := G) K k, MappedComplexExtension.DerivedSections.mapExtendXIso_natCast (G := G) L k]
    rw [Functor.mapHomologicalComplex_map_f]
    simp only [G.map_comp, Iso.trans_hom, MappedComplexExtension.DerivedSections.mapXIso]
    let eK := HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
      (ComplexShape.embeddingUpNat_f k)
    let eL := HomologicalComplex.extendXIso L ComplexShape.embeddingUpNat
      (ComplexShape.embeddingUpNat_f k)
    let gK := HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
      ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)
    let gL := HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj L)
      ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)
    change (G.map eK.hom ≫ G.map (f.f k) ≫ G.map eL.inv) ≫
        (G.map eL.hom ≫ 𝟙 _ ≫ gL.inv) =
      (G.map eK.hom ≫ 𝟙 _ ≫ gK.inv) ≫
        (gK.hom ≫ G.map (f.f k) ≫ gL.inv)
    have heL : G.map eL.inv ≫ G.map eL.hom = 𝟙 _ :=
      (G.mapIso eL).inv_hom_id
    have heLgL : G.map eL.inv ≫ G.map eL.hom ≫ gL.inv = gL.inv :=
      (G.mapIso eL).inv_hom_id_assoc gL.inv
    have hgK : gK.inv ≫ gK.hom ≫ G.map (f.f k) ≫ gL.inv =
        G.map (f.f k) ≫ gL.inv := by
      exact gK.inv_hom_id_assoc (G.map (f.f k) ≫ gL.inv)
    calc
      _ = G.map eK.hom ≫ G.map (f.f k) ≫ gL.inv := by
        have hunit : (𝟙 (G.obj (L.X k))) ≫ gL.inv = gL.inv :=
          Category.id_comp gL.inv
        have htail₀ : G.map eL.hom ≫ 𝟙 _ ≫ gL.inv =
            G.map eL.hom ≫ gL.inv :=
          congrArg (fun q ↦ G.map eL.hom ≫ q) hunit
        have htail : G.map eL.inv ≫
            (G.map eL.hom ≫ 𝟙 _ ≫ gL.inv) = gL.inv :=
          (congrArg (fun q ↦ G.map eL.inv ≫ q) htail₀).trans heLgL
        have houter := Category.assoc
          (G.map eK.hom) (G.map (f.f k) ≫ G.map eL.inv)
          (G.map eL.hom ≫ 𝟙 _ ≫ gL.inv)
        have hinner := Category.assoc (G.map (f.f k)) (G.map eL.inv)
          (G.map eL.hom ≫ 𝟙 _ ≫ gL.inv)
        have hinnerWhisker := congrArg (fun q ↦ G.map eK.hom ≫ q) hinner
        have hcancelWhisker := congrArg
          (fun q ↦ G.map eK.hom ≫ G.map (f.f k) ≫ q) htail
        exact houter.trans (hinnerWhisker.trans hcancelWhisker)
      _ = _ := by
        simp only [Category.assoc]
        apply (cancel_epi (G.mapIso eK).hom).2
        exact hgK.symm
  · exact (((G.mapHomologicalComplex (.up ℕ)).obj L).isZero_extend_X
      ComplexShape.embeddingUpNat n (fun k hk ↦ h ⟨k, hk⟩) |>.eq_of_tgt _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedComplexExtensionNaturality.DerivedSections
