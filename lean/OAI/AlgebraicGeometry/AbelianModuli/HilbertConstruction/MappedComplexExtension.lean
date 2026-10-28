/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafDerivedGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedCohomologyMaps

/-! # Mapped Complex Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedComplexExtension.DerivedSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.CategoryTheory.Abelian.Ext
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]
variable {Z F : C}

def mapXIso (K : CochainComplex C ℕ) (n : ℕ) :
    G.obj (K.X n) ≅ ((G.mapHomologicalComplex (.up ℕ)).obj K).X n :=
  Iso.refl _

lemma mapXIso_naturality (K : CochainComplex C ℕ) (i j : ℕ) :
    (mapXIso K i).hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d i j =
      G.map (K.d i j) ≫ (mapXIso K j).hom :=
  rfl

def mapExtendXIso
    (K : CochainComplex C ℕ) (n : ℤ) :
    G.obj ((K.extend ComplexShape.embeddingUpNat).X n) ≅
      (((G.mapHomologicalComplex (.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat).X n := by
  classical
  exact if h : 0 ≤ n then
      G.mapIso (HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
        (Int.toNat_of_nonneg h)) ≪≫
        mapXIso K n.toNat ≪≫
        (HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
          ComplexShape.embeddingUpNat (Int.toNat_of_nonneg h)).symm
    else
      IsZero.iso
        (G.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat n
          (fun k hk ↦ h (hk ▸ Int.natCast_nonneg k))))
        (((G.mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X
          ComplexShape.embeddingUpNat n (fun k hk ↦ h (hk ▸ Int.natCast_nonneg k)))

lemma mapExtendXIso_natCast (K : CochainComplex C ℕ) (k : ℕ) :
    mapExtendXIso (G := G) K (k : ℤ) =
      G.mapIso (HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat_f k)) ≪≫
        mapXIso (G := G) K k ≪≫
          (HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
            ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)).symm := by
  classical
  simp [mapExtendXIso]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedComplexExtension.DerivedSections
