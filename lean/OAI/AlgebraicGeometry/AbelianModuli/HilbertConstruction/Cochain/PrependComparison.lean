import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroCycles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.HeadCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShortComplexOf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.HeadFunctor

/-! # Prepend Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.PrependComparison.CochainPrependComparison

noncomputable section

/-! Adjoining a compatible first differential to a quasi-isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]
variable {C D : CochainComplex (ModuleCat.{v} R) ℕ} (φ : C ⟶ D)
variable {A : ModuleCat.{v} R} (d : A ⟶ C.X 0) (e : A ⟶ D.X 0)
variable (hd : d ≫ C.d 0 1 = 0) (he : e ≫ D.d 0 1 = 0)
variable (h : 𝟙 A ≫ e = d ≫ φ.f 0)

theorem zero [QuasiIsoAt φ 0] : QuasiIsoAt (Head.CochainHead.consMap (𝟙 A) φ d e hd he h) 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff]
  let ψ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R)
    (ComplexShape.up ℕ) 0 0 1).map (Head.CochainHead.consMap (𝟙 A) φ d e hd he h)
  have hc : IsIso (ShortComplex.cyclesMap ψ) := by
    apply ShortComplexOf.ShortComplexComparison.cycles_iso
    · intro y hy
      change ↥A at y
      change (Head.CochainHead.cons A D e he).d 0 1 y = 0 at hy
      rw [Head.CochainHead.cons_d_zero] at hy
      refine ⟨y, ?_, rfl⟩
      change (Head.CochainHead.cons A C d hd).d 0 1 y = 0
      rw [Head.CochainHead.cons_d_zero]
      let z : (C.d 0 1).hom.ker := ⟨d y, by
        change (d ≫ C.d 0 1) y = 0
        rw [hd]
        rfl⟩
      have hz : z = 0 := (ZeroCycles.CochainZeroCycles.kernelEquiv φ).injective (by
        rw [map_zero]
        apply Subtype.ext
        rw [ZeroCycles.CochainZeroCycles.kernelEquiv_apply_val]
        exact (ConcreteCategory.congr_hom h y).symm.trans hy)
      exact congrArg Subtype.val hz
    · intro x _ hx
      exact hx
  apply ShortComplexOf.ShortComplexComparison.quasiIso_of_cycles_iso ψ
  · exact (Head.CochainHead.cons A C d hd).shape 0 0 (by decide)
  · exact (Head.CochainHead.cons A D e he).shape 0 0 (by decide)

theorem one [QuasiIsoAt φ 0] : QuasiIsoAt (Head.CochainHead.consMap (𝟙 A) φ d e hd he h) 1 := by
  rw [quasiIsoAt_iff' _ 0 1 2 (by simp) (by simp)]
  let ψ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R)
    (ComplexShape.up ℕ) 0 1 2).map (Head.CochainHead.consMap (𝟙 A) φ d e hd he h)
  have hc : IsIso (ShortComplex.cyclesMap ψ) := by
    apply ShortComplexOf.ShortComplexComparison.cycles_iso
    · intro y hy
      change ↥(D.X 0) at y
      change (Head.CochainHead.cons A D e he).d 1 2 y = 0 at hy
      have hy' : D.d 0 1 y = 0 := by simpa [Head.CochainHead.cons, CochainComplex.of.d, Head.CochainHead.consD] using hy
      let x := (ZeroCycles.CochainZeroCycles.kernelEquiv φ).symm ⟨y, hy'⟩
      refine ⟨x.val, ?_, ?_⟩
      · change (Head.CochainHead.cons A C d hd).d 1 2 x.val = 0
        simp [Head.CochainHead.cons, CochainComplex.of.d, Head.CochainHead.consD]
      · change φ.f 0 x.val = y
        rw [← ZeroCycles.CochainZeroCycles.kernelEquiv_apply_val]
        exact congrArg Subtype.val ((ZeroCycles.CochainZeroCycles.kernelEquiv φ).apply_symm_apply ⟨y, hy'⟩)
    · intro x hx hf
      change ↥(C.X 0) at x
      change (Head.CochainHead.cons A C d hd).d 1 2 x = 0 at hx
      have hx' : C.d 0 1 x = 0 := by simpa [Head.CochainHead.cons, CochainComplex.of.d, Head.CochainHead.consD] using hx
      have hz : (⟨x, hx'⟩ : (C.d 0 1).hom.ker) = 0 :=
        (ZeroCycles.CochainZeroCycles.kernelEquiv φ).injective (by
          rw [map_zero]
          apply Subtype.ext
          rw [ZeroCycles.CochainZeroCycles.kernelEquiv_apply_val]
          exact hf)
      exact congrArg Subtype.val hz
  have : Epi ψ.τ₁ := inferInstanceAs (Epi (𝟙 A))
  exact ⟨ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi hc inferInstance⟩

theorem quasiIso [QuasiIso φ] : QuasiIso (Head.CochainHead.consMap (𝟙 A) φ d e hd he h) := by
  constructor
  intro n
  rcases n with _ | _ | n
  · exact zero φ d e hd he h
  · exact one φ d e hd he h
  · exact HeadCohomology.CochainHead.consMap_quasiIso_higher (𝟙 A) φ d e hd he h n

theorem mapped_quasiIso (F : ModuleCat.{v} R ⥤ ModuleCat.{v} R) [F.PreservesZeroMorphisms]
    [QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)] :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (Head.CochainHead.consMap (𝟙 A) φ d e hd he h)) := by
  let φ' := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ
  have h' : 𝟙 (F.obj A) ≫ F.map e = F.map d ≫ φ'.f 0 := by
    change 𝟙 (F.obj A) ≫ F.map e = F.map d ≫ F.map (φ.f 0)
    rw [← F.map_comp, ← h, Category.id_comp, Category.id_comp]
  have H : QuasiIso (Head.CochainHead.consMap (𝟙 (F.obj A)) φ' (F.map d) (F.map e)
      (HeadFunctor.CochainHead.mapped_square F d hd) (HeadFunctor.CochainHead.mapped_square F e he) h') :=
    quasiIso φ' _ _ _ _ _
  apply (quasiIso_iff_of_arrow_mk_iso _ _ (HeadFunctor.CochainHead.mapConsArrowIso F (𝟙 A) φ d e hd he h)).mpr
  convert H using 1
  ext n : 1
  cases n <;> simp [Head.CochainHead.consMap, φ']

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.PrependComparison.CochainPrependComparison
