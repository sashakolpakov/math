import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Injective First -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveFirst.InjectiveFirstCycles

noncomputable section

/-!
# The first cycles of an injective resolution

The augmentation identifies the original object with the kernel of the
surjection from degree zero onto the degree-one cycles. This packages the
initial part of the original injective resolution as a short exact sequence.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] {F : C} (I : InjectiveResolution F)

theorem augmentation_toCycles : I.ι.f 0 ≫ (I.cocomplex.sc' 0 1 2).toCycles = 0 := by
  apply (cancel_mono (I.cocomplex.sc' 0 1 2).iCycles).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => I.ι.f 0 ≫ f) (I.cocomplex.sc' 0 1 2).toCycles_i).trans
      (I.ι_f_zero_comp_complex_d.trans (zero_comp :
        (0 : F ⟶ (I.cocomplex.sc' 0 1 2).cycles) ≫ (I.cocomplex.sc' 0 1 2).iCycles = 0).symm))

def shortComplex : ShortComplex C :=
  ShortComplex.mk (I.ι.f 0) (I.cocomplex.sc' 0 1 2).toCycles (augmentation_toCycles I)

def comparison : shortComplex I ⟶ ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d :=
  ShortComplex.Hom.mk (𝟙 _) (𝟙 _) (I.cocomplex.sc' 0 1 2).iCycles
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (I.cocomplex.sc' 0 1 2).toCycles_i.symm)

theorem shortExact : (shortComplex I).ShortExact := by
  have hI : (I.cocomplex.sc' 0 1 2).Exact :=
    (I.cocomplex.exactAt_iff' 0 1 2 (by simp) (by simp)).mp (I.cocomplex_exactAt_succ 0)
  have : Epi (I.cocomplex.sc' 0 1 2).toCycles := hI.epi_toCycles
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · have : Epi (comparison I).τ₁ := by change Epi (𝟙 F); infer_instance
    have : IsIso (comparison I).τ₂ := by change IsIso (𝟙 (I.cocomplex.X 0)); infer_instance
    have : Mono (comparison I).τ₃ := by change Mono (I.cocomplex.sc' 0 1 2).iCycles; infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono (comparison I)).mpr I.exact₀
  · change Mono (I.ι.f 0)
    infer_instance
  · change Epi (I.cocomplex.sc' 0 1 2).toCycles
    infer_instance

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveFirst.InjectiveFirstCycles
