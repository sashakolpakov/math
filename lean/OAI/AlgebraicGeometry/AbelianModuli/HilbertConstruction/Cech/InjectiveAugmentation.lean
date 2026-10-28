/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechInjectiveAugmentation.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.CochainExactness

/-! # Injective Augmentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveAugmentation.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- The native Cech map induced by the augmentation into the chosen injective
resolution. -/
noncomputable def cechInjectiveResolutionAugmentation
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (cechComplexFunctor U).obj F.obj ⟶
      (InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).X 0 :=
  (cechComplexFunctor U).map
    ((injectiveResolution F).ι.f 0).hom

@[simp]
theorem cechInjectiveResolutionAugmentation_f
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (p : ℕ) :
    (cechInjectiveResolutionAugmentation U F).f p =
      ((cechComplexFunctor U).map
        ((injectiveResolution F).ι.f 0).hom).f p :=
  rfl

@[reassoc]
theorem cechInjectiveResolutionAugmentation_f_comp_d
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (p : ℕ) :
    (cechInjectiveResolutionAugmentation U F).f p ≫
      ((InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).d 0 1).f p = 0 := by
  let I := injectiveResolution F
  have h :
      (I.ι.f 0).hom ≫ (I.cocomplex.d 0 1).hom = 0 := by
    exact congrArg (fun f ↦ f.hom)
      (InjectiveResolution.ι_f_zero_comp_complex_d I)
  change Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
      (I.ι.f 0).hom.app
        (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))) ≫
    Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
      (I.cocomplex.d 0 1).hom.app
        (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))) = 0
  rw [Limits.Pi.map_comp_map]
  refine Limits.Pi.hom_ext _ _ fun i ↦ ?_
  rw [Limits.Pi.map_π]
  have hi := congr_app h
    (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))
  have hi' :
      (I.ι.f 0).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) ≫
        (I.cocomplex.d 0 1).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) = 0 := by
    change ((I.ι.f 0).hom ≫ (I.cocomplex.d 0 1).hom).app _ = 0
    exact hi.trans rfl
  rw [hi', comp_zero, zero_comp]

noncomputable instance cechInjectiveResolutionAugmentation_f_mono
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (p : ℕ) :
    Mono ((cechInjectiveResolutionAugmentation U F).f p) := by
  change Mono (Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
    ((injectiveResolution F).ι.f 0).hom.app
      (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))))
  infer_instance

theorem cechInjectiveResolutionAugmentation_exact
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (p : ℕ) :
    (ShortComplex.mk ((cechInjectiveResolutionAugmentation U F).f p)
      (((InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).d 0 1).f p)
      (cechInjectiveResolutionAugmentation_f_comp_d U F p)).Exact := by
  let I : InjectiveResolution F := injectiveResolution F
  let S := ShortComplex.mk (I.ι.f 0) (I.cocomplex.d 0 1) I.ι_f_zero_comp_complex_d
  change (S.map (CochainExactness.IntrinsicCech.cechCochainFunctor U p)).Exact
  apply CochainExactness.IntrinsicCech.cechCochainFunctor_exact_of_sections
  intro i x hx
  exact TopCat.Sheaf.sections_exact_of_left_exact I.exact₀
    (inferInstance : Mono S.f) x hx

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveAugmentation.IntrinsicCech
