import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.FormRestriction
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.ExtensionNaturality

/-! # Open Nat Complex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.OpenNatComplex

noncomputable section

/-! The original nonnegative algebraic de Rham pullback is invertible across open immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsOpenImmersion f.left]

def algebraicOptionSheafPullback (o : Option ℕ) :=
  ((Sheaves.imageAdjunction f).homEquiv
    ((presheafToSheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ)).obj
      (ExtensionNaturality.algebraicOptionPresheaf Y o))
    ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).obj
      (ExtensionNaturality.algebraicOptionPresheaf X o))).symm (ExtensionNaturality.algebraicOptionSheafDirectImage f o)

theorem deRhamSheafPullback_isIso_of_openImmersion : IsIso (Sheaf.CochainPullback.deRhamSheafPullback f) := by
  have : IsIso (OpenForms.deRhamSheafPullbackInt f) := FormRestriction.deRhamSheafPullbackInt_isIso_of_openImmersion f
  have (n : ℕ) : IsIso ((Sheaf.CochainPullback.deRhamSheafPullback f).f n) := by
    have h : IsIso (algebraicOptionSheafPullback f ((ComplexShape.embeddingUpIntGE 0).r (n : ℤ))) := by
      change IsIso ((OpenForms.deRhamSheafPullbackInt f).f (n : ℤ))
      infer_instance
    have hn : (ComplexShape.embeddingUpIntGE 0).r (n : ℤ) = some n :=
      (ComplexShape.embeddingUpIntGE 0).r_eq_some (by simp [ComplexShape.embeddingUpIntGE])
    rw [hn] at h
    exact h
  exact HomologicalComplex.Hom.isIso_of_components _

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.OpenNatComplex
