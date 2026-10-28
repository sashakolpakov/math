import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionHomotopy

/-! # Augmented Injective -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentedInjective.AugmentedInjectiveComparison

noncomputable section

/-! A typed interface for comparison of an augmented resolution with
an injective resolution, with the quasi-isomorphism premise explicit. -/

open _root_.CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {Z : C} (K : CochainComplex C ℕ) (a : (CochainComplex.single₀ C).obj Z ⟶ K)
  (h : QuasiIso a) (I : InjectiveResolution Z)

def map : K ⟶ I.cocomplex := @IntegralComparison.Augmented.ResolutionToInjective.map C _ _ K Z Z a h I (𝟙 Z)

theorem augmentation : a ≫ map K a h I = I.ι := by
  let := h
  exact (IntegralComparison.Augmented.ResolutionToInjective.augmentation K a I (𝟙 Z)).trans
    ((congrArg (fun b => b ≫ I.ι) ((CochainComplex.single₀ C).map_id Z)).trans (Category.id_comp _))

theorem quasiIso : QuasiIso (map K a h I) := by
  let := h
  exact IntegralComparison.Augmented.ResolutionToInjective.quasiIso K a I (𝟙 Z)

def homotopy (b : K ⟶ I.cocomplex) (hb : a ≫ b = I.ι) : Homotopy (map K a h I) b := by
  let := h
  exact IntegralComparison.Augmented.ResolutionHomotopy.homotopy K a I (map K a h I) b
    ((augmentation K a h I).trans hb.symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentedInjective.AugmentedInjectiveComparison
