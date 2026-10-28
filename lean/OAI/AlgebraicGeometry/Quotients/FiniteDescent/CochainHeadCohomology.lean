import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainHeadD

/-! # Cochain Head Cohomology -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainHeadCohomology

noncomputable section

/-! Positive cohomology under adjoining or removing the first term. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

namespace Construction.CochainHead

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

def consWindowIso (A : V) (C : CochainComplex V ℕ) (d : A ⟶ C.X 0)
    (h : d ≫ C.d 0 1 = 0) (i j k : ℕ) :
    (CochainHeadD.Construction.CochainHead.cons A C d h).sc' (i + 1) (j + 1) (k + 1) ≅ C.sc' i j k :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change 𝟙 (C.X i) ≫ C.d i j = (CochainHeadD.Construction.CochainHead.cons A C d h).d (i + 1) (j + 1) ≫ 𝟙 (C.X j)
      rw [Category.id_comp, Category.comp_id]
      exact (CochainHeadD.Construction.CochainHead.cons_d_succ A C d h i j).symm)
    (by
      change 𝟙 (C.X j) ≫ C.d j k = (CochainHeadD.Construction.CochainHead.cons A C d h).d (j + 1) (k + 1) ≫ 𝟙 (C.X k)
      rw [Category.id_comp, Category.comp_id]
      exact (CochainHeadD.Construction.CochainHead.cons_d_succ A C d h j k).symm)

def consWindowArrowIso {A B : V} {C D : CochainComplex V ℕ} (f : A ⟶ B) (φ : C ⟶ D)
    (d : A ⟶ C.X 0) (e : B ⟶ D.X 0)
    (hd : d ≫ C.d 0 1 = 0) (he : e ≫ D.d 0 1 = 0)
    (h : f ≫ e = d ≫ φ.f 0) (i j k : ℕ) :
    Arrow.mk ((HomologicalComplex.shortComplexFunctor' V (ComplexShape.up ℕ)
      (i + 1) (j + 1) (k + 1)).map (CochainHeadD.Construction.CochainHead.consMap f φ d e hd he h)) ≅
        Arrow.mk ((HomologicalComplex.shortComplexFunctor' V (ComplexShape.up ℕ) i j k).map φ) :=
  Arrow.isoMk (consWindowIso A C d hd i j k) (consWindowIso B D e he i j k) (by
    ext <;> simp [consWindowIso, CochainHeadD.Construction.CochainHead.consMap])

variable [CategoryWithHomology V]

def tailHomologyIso (C : CochainComplex V ℕ) (n : ℕ) :
    (CochainHeadD.Construction.CochainHead.tail C).homology (n + 1) ≅ C.homology (n + 2) :=
  (CochainHeadD.Construction.CochainHead.tail C).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (CochainHeadD.Construction.CochainHead.tailWindowIso C n (n + 1) (n + 2)) ≪≫
      (C.homologyIsoSc' (n + 1) (n + 2) (n + 3) (by simp) (by simp)).symm

theorem consMap_quasiIso_higher {A B : V} {C D : CochainComplex V ℕ} (f : A ⟶ B) (φ : C ⟶ D)
    (d : A ⟶ C.X 0) (e : B ⟶ D.X 0)
    (hd : d ≫ C.d 0 1 = 0) (he : e ≫ D.d 0 1 = 0)
    (h : f ≫ e = d ≫ φ.f 0) (n : ℕ) [QuasiIsoAt φ (n + 1)] :
    QuasiIsoAt (CochainHeadD.Construction.CochainHead.consMap f φ d e hd he h) (n + 2) := by
  rw [quasiIsoAt_iff' _ (n + 1) (n + 2) (n + 3) (by simp) (by simp)]
  have hφ : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor' V (ComplexShape.up ℕ) n (n + 1) (n + 2)).map φ) :=
    (quasiIsoAt_iff' φ n (n + 1) (n + 2) (by simp) (by simp)).mp inferInstance
  exact ShortComplex.quasiIso_of_arrow_mk_iso _ _
    (consWindowArrowIso f φ d e hd he h n (n + 1) (n + 2)).symm

end Construction.CochainHead

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainHeadCohomology
