/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafDerivedGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.HomComplexSections
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Resolution Extension Sections -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ResolutionExtensionSections

noncomputable section

/-! Actual additive global sections commute with extension of a nonnegative resolution by zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]

def resolutionMapXIso (K : CochainComplex C ℕ) (n : ℕ) :
    G.obj (K.X n) ≅ ((G.mapHomologicalComplex (.up ℕ)).obj K).X n :=
  Iso.refl _

theorem resolutionMapXIso_naturality (K : CochainComplex C ℕ) (i j : ℕ) :
    (resolutionMapXIso K i).hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d i j =
      G.map (K.d i j) ≫ (resolutionMapXIso K j).hom :=
  rfl

def resolutionMapExtendXIso
    (K : CochainComplex C ℕ) (n : ℤ) :
    G.obj ((K.extend ComplexShape.embeddingUpNat).X n) ≅
      (((G.mapHomologicalComplex (.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat).X n := by
  classical
  exact if h : 0 ≤ n then
      G.mapIso (HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
        (Int.toNat_of_nonneg h)) ≪≫
        resolutionMapXIso K n.toNat ≪≫
        (HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
          ComplexShape.embeddingUpNat (Int.toNat_of_nonneg h)).symm
    else
      IsZero.iso
        (G.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat n
          (fun k hk ↦ h (hk ▸ Int.natCast_nonneg k))))
        (((G.mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X
          ComplexShape.embeddingUpNat n (fun k hk ↦ h (hk ▸ Int.natCast_nonneg k)))

theorem resolutionMapExtendXIso_natCast (K : CochainComplex C ℕ) (k : ℕ) :
    resolutionMapExtendXIso (G := G) K (k : ℤ) =
      G.mapIso (HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat_f k)) ≪≫
        resolutionMapXIso (G := G) K k ≪≫
          (HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
            ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)).symm := by
  classical
  simp [resolutionMapExtendXIso]

def resolutionMapExtendIso (K : CochainComplex C ℕ) :
    (G.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((G.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents (resolutionMapExtendXIso K) fun i j hij ↦ by
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
        rw [resolutionMapExtendXIso_natCast (G := G) K a, resolutionMapExtendXIso_natCast (G := G) K b]
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
        let mᵢ := resolutionMapXIso (G := G) K a
        let mⱼ := resolutionMapXIso (G := G) K b
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
              exact resolutionMapXIso_naturality K a b]
          _ = _ := by simp [Functor.map_comp, Category.assoc]
      · exact (((G.mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X
          ComplexShape.embeddingUpNat j (fun k hk ↦ hj ⟨k, hk⟩) |>.eq_of_tgt _ _)
    · exact (G.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat i
        (fun k hk ↦ hi ⟨k, hk⟩)) |>.eq_of_src _ _)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ResolutionExtensionSections
