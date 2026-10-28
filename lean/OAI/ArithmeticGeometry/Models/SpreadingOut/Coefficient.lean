import OAI.ArithmeticGeometry.Models.SpreadingOut.CoefficientSmoothness
import OAI.ArithmeticGeometry.Models.BaseChange

/-! # Coefficient -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.Coefficient.Construction

noncomputable section

/-! A proper coefficient model of a smooth scheme gives the exact
smooth-proper arithmetic model required in SpreadingOut. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

open OAI.ArithmeticGeometry.Models.BaseChange.Constructions.Foundations

theorem smooth_proper_coefficient_model_to_arithmetic
    {K : Type u} [Field K] [NumberField K]
    {X : Over (Spec (.of K))} (M : Foundations.Constructions.CoefficientModel K X)
    [Smooth M.model.hom] [IsProper M.model.hom] :
    ∃ (B : Base.Construction.ArithmeticOpen K) (N : Over B.U.toScheme),
      Smooth N.hom ∧ IsProper N.hom ∧
      Nonempty ((Over.pullback B.generic).obj N ≅ X) := by
  let A := CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K M.coefficients
  obtain ⟨d, hd, hpow, hle⟩ := Fg.Construction.fg_subalgebra_le_localization A
    ⟨M.coefficients, rfl⟩
  let R₀ := Localization.subalgebra.ofField K (Submonoid.powers d) hpow
  let φ : A →ₐ[𝓞 K] R₀ := Subalgebra.inclusion hle
  let f := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let M₀ := (Over.pullback f).obj M.model
  let g := Spec.map (CommRingCat.ofHom (algebraMap R₀ K))
  have hgf : g ≫ f = CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K M.coefficients := by
    rw [← Spec.map_comp]
    rfl
  let B := Base.Construction.arithmeticOpenOfNonzero K d hd
  let j : Spec (.of R₀) ≅ B.U.toScheme := Affine.Construction.localizationOpenIso (𝓞 K) R₀ d
  let N := (Over.map j.hom).obj M₀
  have hj : j.hom ≫ B.U.ι = Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) R₀)) :=
    Affine.Construction.localizationOpenIso_hom_ι (𝓞 K) R₀ d
  have hg : g ≫ j.hom = B.generic := by
    apply (cancel_mono B.U.ι).mp
    rw [Category.assoc, hj, B.generic_eq]
    change Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) R₀)) = _
    rw [← Spec.map_comp]
    congr 1
  have : Smooth M₀.hom := inferInstanceAs (Smooth (pullback.snd M.model.hom f))
  have : IsProper M₀.hom := inferInstanceAs (IsProper (pullback.snd M.model.hom f))
  refine ⟨B, N, ?_, ?_, ?_⟩
  · change Smooth (M₀.hom ≫ j.hom)
    infer_instance
  · change IsProper (M₀.hom ≫ j.hom)
    infer_instance
  · rw [← hg]
    exact ⟨Affine.Construction.baseChangeAlongIso M₀ j g ≪≫ BaseChange.Constructions.Foundations.iteratedBaseChangeIso f g M.model ≪≫
      Scheme.Constructions.Foundations.baseChangeCongr hgf M.model ≪≫ M.genericIso⟩

/-- Properness is the only remaining model-existence obligation for the
first SpreadingOut conclusion: generic smoothness supplies smoothness after shrinking. -/
theorem proper_coefficient_model_to_arithmetic
    {K : Type u} [Field K] [NumberField K]
    {X : Over (Spec (.of K))} [Smooth X.hom]
    (M : Foundations.Constructions.CoefficientModel K X) [IsProper M.model.hom] :
    ∃ (B : Base.Construction.ArithmeticOpen K) (N : Over B.U.toScheme),
      Smooth N.hom ∧ IsProper N.hom ∧
      Nonempty ((Over.pullback B.generic).obj N ≅ X) := by
  have : IsIso M.genericIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map M.genericIso.hom))
  have hs : Smooth (M.genericIso.hom.left ≫ X.hom) := inferInstance
  rw [M.genericIso.hom.w] at hs
  have := hs
  obtain ⟨t, h, hsm⟩ := CoefficientSmoothness.Construction.proper_coefficient_model_eventually_smooth M.model
  let N := M.enlarge t h
  have : Smooth N.model.hom := hsm
  have : IsProper N.model.hom :=
    inferInstanceAs (IsProper (pullback.snd M.model.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)))
  exact smooth_proper_coefficient_model_to_arithmetic N

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.Coefficient.Construction
