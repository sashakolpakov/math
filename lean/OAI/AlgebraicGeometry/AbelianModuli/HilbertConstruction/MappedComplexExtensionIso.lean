/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafDerivedGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedComplexExtension

/-! # Mapped Complex Extension Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedComplexExtensionIso.DerivedSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.CategoryTheory.Abelian.Ext
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]
variable {Z F : C}

def mapExtendIso (K : CochainComplex C ℕ) :
    (G.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((G.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents (MappedComplexExtension.DerivedSections.mapExtendXIso K) fun i j hij ↦ by
    clear hij
    by_cases hi : ∃ k, ComplexShape.embeddingUpNat.f k = i
    · obtain ⟨a, ha⟩ := hi
      have ha' : (a : ℤ) = i := (ComplexShape.embeddingUpNat_f a).symm.trans ha
      clear ha
      subst i
      by_cases hj : ∃ k, ComplexShape.embeddingUpNat.f k = j
      · obtain ⟨b, hb⟩ := hj
        have hb' : (b : ℤ) = j := (ComplexShape.embeddingUpNat_f b).symm.trans hb
        clear hb
        subst j
        rw [MappedComplexExtension.DerivedSections.mapExtendXIso_natCast (G := G) K a, MappedComplexExtension.DerivedSections.mapExtendXIso_natCast (G := G) K b]
        rw [Functor.mapHomologicalComplex_obj_d,
          HomologicalComplex.extend_d_eq ((G.mapHomologicalComplex (.up ℕ)).obj K)
            ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f a)
              (ComplexShape.embeddingUpNat_f b),
          HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat
            (ComplexShape.embeddingUpNat_f a) (ComplexShape.embeddingUpNat_f b)]
        let eᵢ := HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
          (ComplexShape.embeddingUpNat_f a)
        let eⱼ := HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
          (ComplexShape.embeddingUpNat_f b)
        let fᵢ := HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f a)
        let fⱼ := HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f b)
        let mᵢ := MappedComplexExtension.DerivedSections.mapXIso (G := G) K a
        let mⱼ := MappedComplexExtension.DerivedSections.mapXIso (G := G) K b
        change (G.map eᵢ.hom ≫ mᵢ.hom ≫ fᵢ.inv) ≫
            (fᵢ.hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d
              a b ≫ fⱼ.inv) =
          G.map (eᵢ.hom ≫ K.d a b ≫ eⱼ.inv) ≫
            (G.map eⱼ.hom ≫ mⱼ.hom ≫ fⱼ.inv)
        calc
          _ = G.map eᵢ.hom ≫
              (mᵢ.hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d
                a b) ≫ fⱼ.inv := by
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
          _ = G.map eᵢ.hom ≫
              (G.map (K.d a b) ≫ mⱼ.hom) ≫ fⱼ.inv := by
            rw [show mᵢ.hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d
                a b = G.map (K.d a b) ≫ mⱼ.hom by
              exact MappedComplexExtension.DerivedSections.mapXIso_naturality K a b]
          _ = _ := by simp [Functor.map_comp, Category.assoc]
      · exact (((G.mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X
          ComplexShape.embeddingUpNat j (fun k hk ↦ hj ⟨k, hk⟩) |>.eq_of_tgt _ _)
    · exact (G.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat i
        (fun k hk ↦ hi ⟨k, hk⟩)) |>.eq_of_src _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedComplexExtensionIso.DerivedSections
