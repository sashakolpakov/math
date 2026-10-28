import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.Head

/-! # Head Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.HeadCohomology.CochainHead

noncomputable section

/-! Positive cohomology under adjoining or removing the first term. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

def consWindowIso (A : V) (C : CochainComplex V ℕ) (d : A ⟶ C.X 0)
    (h : d ≫ C.d 0 1 = 0) (i j k : ℕ) :
    (Head.CochainHead.cons A C d h).sc' (i + 1) (j + 1) (k + 1) ≅ C.sc' i j k :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change 𝟙 (C.X i) ≫ C.d i j = (Head.CochainHead.cons A C d h).d (i + 1) (j + 1) ≫ 𝟙 (C.X j)
      rw [Category.id_comp, Category.comp_id]
      exact (Head.CochainHead.cons_d_succ A C d h i j).symm)
    (by
      change 𝟙 (C.X j) ≫ C.d j k = (Head.CochainHead.cons A C d h).d (j + 1) (k + 1) ≫ 𝟙 (C.X k)
      rw [Category.id_comp, Category.comp_id]
      exact (Head.CochainHead.cons_d_succ A C d h j k).symm)

def consWindowArrowIso {A B : V} {C D : CochainComplex V ℕ} (f : A ⟶ B) (φ : C ⟶ D)
    (d : A ⟶ C.X 0) (e : B ⟶ D.X 0)
    (hd : d ≫ C.d 0 1 = 0) (he : e ≫ D.d 0 1 = 0)
    (h : f ≫ e = d ≫ φ.f 0) (i j k : ℕ) :
    Arrow.mk ((HomologicalComplex.shortComplexFunctor' V (ComplexShape.up ℕ)
      (i + 1) (j + 1) (k + 1)).map (Head.CochainHead.consMap f φ d e hd he h)) ≅
        Arrow.mk ((HomologicalComplex.shortComplexFunctor' V (ComplexShape.up ℕ) i j k).map φ) :=
  Arrow.isoMk (consWindowIso A C d hd i j k) (consWindowIso B D e he i j k) (by
    ext
    · exact (Category.id_comp (φ.f i)).trans (Category.comp_id (φ.f i)).symm
    · exact (Category.id_comp (φ.f j)).trans (Category.comp_id (φ.f j)).symm
    · exact (Category.id_comp (φ.f k)).trans (Category.comp_id (φ.f k)).symm)

variable [CategoryWithHomology V]

def tailHomologyIso (C : CochainComplex V ℕ) (n : ℕ) :
    (Head.CochainHead.tail C).homology (n + 1) ≅ C.homology (n + 2) :=
  (Head.CochainHead.tail C).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (Head.CochainHead.tailWindowIso C n (n + 1) (n + 2)) ≪≫
      (C.homologyIsoSc' (n + 1) (n + 2) (n + 3) (by simp) (by simp)).symm

theorem consMap_quasiIso_higher {A B : V} {C D : CochainComplex V ℕ} (f : A ⟶ B) (φ : C ⟶ D)
    (d : A ⟶ C.X 0) (e : B ⟶ D.X 0)
    (hd : d ≫ C.d 0 1 = 0) (he : e ≫ D.d 0 1 = 0)
    (h : f ≫ e = d ≫ φ.f 0) (n : ℕ) [QuasiIsoAt φ (n + 1)] :
    QuasiIsoAt (Head.CochainHead.consMap f φ d e hd he h) (n + 2) := by
  rw [quasiIsoAt_iff' _ (n + 1) (n + 2) (n + 3) (by simp) (by simp)]
  have hφ : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor' V (ComplexShape.up ℕ) n (n + 1) (n + 2)).map φ) :=
    (quasiIsoAt_iff' φ n (n + 1) (n + 2) (by simp) (by simp)).mp inferInstance
  exact ShortComplex.quasiIso_of_arrow_mk_iso _ _
    (consWindowArrowIso f φ d e hd he h n (n + 1) (n + 2)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.HeadCohomology.CochainHead
