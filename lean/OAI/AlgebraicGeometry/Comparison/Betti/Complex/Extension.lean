import Mathlib

/-! # Extension -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension

noncomputable section

/-!
# Extension of complexes commutes with additive functors

The comparison is the identity in degrees already present, and the canonical
zero-object isomorphism in the remaining degrees. It preserves differentials
and is natural in the original complex.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

def mapXIso (K : HomologicalComplex C c) (i : Option ι) :
    F.obj (HomologicalComplex.extend.X K i) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) i :=
  match i with
  | some _ => Iso.refl _
  | none => F.mapZeroObject

theorem mapXIso_d (K : HomologicalComplex C c) (i j : Option ι) :
    (mapXIso F K i).hom ≫ HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) i j =
      F.map (HomologicalComplex.extend.d K i j) ≫ (mapXIso F K j).hom := by
  cases i with
  | none => exact (F.map_isZero (isZero_zero C)).eq_of_src _ _
  | some i =>
    cases j with
    | none => exact (isZero_zero D).eq_of_tgt _ _
    | some j =>
      change 𝟙 (F.obj (K.X i)) ≫ F.map (K.d i j) = F.map (K.d i j) ≫ 𝟙 (F.obj (K.X j))
      simp only [Category.id_comp, Category.comp_id]

/-- The canonical comparison of actual extended complexes. -/
def mapExtendIso (e : c.Embedding c') (K : HomologicalComplex C c) :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (fun i => mapXIso F K (e.r i))
    (fun i j _ => mapXIso_d F K (e.r i) (e.r j))

theorem mapXIso_naturality {K L : HomologicalComplex C c} (φ : K ⟶ L) (i : Option ι) :
    F.map (HomologicalComplex.extend.mapX φ i) ≫ (mapXIso F L i).hom =
      (mapXIso F K i).hom ≫
        HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map φ) i := by
  cases i with
  | none => exact (isZero_zero D).eq_of_tgt _ _
  | some i =>
    change F.map (φ.f i) ≫ 𝟙 (F.obj (L.X i)) = 𝟙 (F.obj (K.X i)) ≫ F.map (φ.f i)
    simp only [Category.id_comp, Category.comp_id]

theorem mapExtendIso_naturality (e : c.Embedding c')
    {K L : HomologicalComplex C c} (φ : K ⟶ L) :
    (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e) ≫
        (mapExtendIso F e L).hom =
      (mapExtendIso F e K).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map φ) e := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact mapXIso_naturality F φ (e.r i)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension
