import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.LeftHomologyIso
import Mathlib.Algebra.Homology.SingleHomology

/-! # Zero Homology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ZeroHomology.MappedZeroHomology

noncomputable section

/-! # Canonical homology of zero-differential complexes under exact transport -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  (S : ShortComplex C) (T : ShortComplex D) (φ : T ⟶ S.map F)
  (hf : S.f = 0) (hg : S.g = 0) (hf' : T.f = 0) (hg' : T.g = 0)

def data : ShortComplex.LeftHomologyMapData φ
    (ShortComplex.LeftHomologyData.ofZeros T hf' hg')
    ((ShortComplex.LeftHomologyData.ofZeros S hf hg).map F) where
  φK := φ.τ₂
  φH := φ.τ₂
  commi := by
    let m : T.X₂ ⟶ F.obj S.X₂ := φ.τ₂
    change m ≫ F.map (𝟙 S.X₂) = 𝟙 T.X₂ ≫ m
    rw [F.map_id, Category.comp_id, Category.id_comp]
  commf' := by
    simp only [ShortComplex.LeftHomologyData.ofZeros_f', ShortComplex.LeftHomologyData.map_f',
      Functor.map_zero]
    let m : T.X₂ ⟶ F.obj S.X₂ := φ.τ₂
    let n : T.X₁ ⟶ F.obj S.X₁ := φ.τ₁
    change (0 : T.X₁ ⟶ T.X₂) ≫ m = n ≫ (0 : F.obj S.X₁ ⟶ F.obj S.X₂)
    rw [zero_comp, comp_zero]
  commπ := by
    let m : T.X₂ ⟶ F.obj S.X₂ := φ.τ₂
    change 𝟙 T.X₂ ≫ m = m ≫ F.map (𝟙 S.X₂)
    rw [F.map_id, Category.comp_id, Category.id_comp]

theorem naturality : ShortComplex.homologyMap φ ≫ (S.mapHomologyIso F).hom ≫
      F.map (ShortComplex.LeftHomologyData.ofZeros S hf hg).homologyIso.hom =
    (ShortComplex.LeftHomologyData.ofZeros T hf' hg').homologyIso.hom ≫ φ.τ₂ := by
  rw [LeftHomologyIso.MappedLeftHomologyIso.homologyIso]
  exact (data F S T φ hf hg hf' hg').homologyMap_comm

variable (A : C)

def singleData : (((CochainComplex.single₀ C).obj A).sc 0).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofZeros _ rfl rfl

theorem singleData_projection : ((CochainComplex.single₀ C).obj A).homologyπ 0 ≫
    (singleData A).homologyIso.hom = ((CochainComplex.single₀ C).obj A).iCycles 0 := by
  have h := (singleData A).homologyπ_comp_homologyIso_hom
  exact h.trans (singleData A).cyclesIso_hom_comp_i

theorem singleData_original : (singleData A).homologyIso.hom ≫
      (HomologicalComplex.singleObjXSelf (.up ℕ) 0 A).hom =
    (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 A).hom := by
  let K := (CochainComplex.single₀ C).obj A
  let e : K.homology 0 ≅ K.X 0 := (singleData A).homologyIso
  let x : K.X 0 ≅ A := HomologicalComplex.singleObjXSelf (.up ℕ) 0 A
  let s : K.homology 0 ≅ A := HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 A
  have hp : K.homologyπ 0 ≫ e.hom = K.iCycles 0 := singleData_projection A
  have hs : K.homologyπ 0 ≫ s.hom = K.iCycles 0 ≫ x.hom :=
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom (.up ℕ) 0 A
  change e.hom ≫ x.hom = s.hom
  apply (cancel_epi (K.homologyπ 0)).mp
  rw [← Category.assoc, hp, hs]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ZeroHomology.MappedZeroHomology
