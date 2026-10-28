import OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveAugmentationQuasi
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SingleAugmentation

/-! # Injective Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.InjectiveAugmentation.MappedInjectiveAugmentation

noncomputable section

/-! # Exact augmented additive images of a resolution of an injective object -/

open _root_.CategoryTheory Limits

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {A : C} [Injective A] (I : InjectiveResolution A) (G : C ⥤ D) [G.Additive]

def augmentation : (CochainComplex.single₀ D).obj (G.obj A) ⟶
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex :=
  (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app A ≫
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι

omit [Injective A] in
theorem component : (augmentation I G).f 0 = G.map (I.ι.f 0) :=
  Category.id_comp _

theorem quasiIso : QuasiIso (augmentation I G) := by
  have := InjectiveAugmentationQuasi.InjectiveAugmentation.map_quasiIso I G
  exact quasiIso_comp _ _

omit [Injective A] in
theorem component_comp_d : G.map (I.ι.f 0) ≫ G.map (I.cocomplex.d 0 1) = 0 := by
  rw [← G.map_comp, I.ι_f_zero_comp_complex_d, G.map_zero]

theorem exact_mono :
    (ShortComplex.mk (G.map (I.ι.f 0)) (G.map (I.cocomplex.d 0 1))
      (component_comp_d I G)).Exact ∧ Mono (G.map (I.ι.f 0)) := by
  let f := (G.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  let g := (HomologicalComplex.shortComplexFunctor' D (ComplexShape.up ℕ) 0 0 1).map f
  have hg : ShortComplex.QuasiIso g :=
    (quasiIsoAt_iff' f 0 0 1 (by simp) (by simp)).mp
      ((InjectiveAugmentationQuasi.InjectiveAugmentation.map_quasiIso I G).quasiIsoAt 0)
  exact (ShortComplex.quasiIso_iff_of_zeros g
    (by simp; rfl) (by simp; exact G.map_zero _ _) (by simp; rfl)).mp hg

theorem exactAt_succ (n : ℕ) :
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).ExactAt (n + 1) := by
  have : QuasiIsoAt (augmentation I G) (n + 1) := (quasiIso I G).quasiIsoAt (n + 1)
  exact (exactAt_iff_of_quasiIsoAt (augmentation I G) (n + 1)).mp
    (CochainComplex.exactAt_succ_single_obj _ n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.InjectiveAugmentation.MappedInjectiveAugmentation
