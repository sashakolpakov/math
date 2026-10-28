import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.RestrictionTorsion

/-! # Iterated Module Fractions -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedModuleFractions.GradedModules

noncomputable section

/-! Common denominator representatives for two successive actual module localizations. -/

universe u v

variable {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]

theorem moduleFractionMap_cancel (a : A) (k : ℕ) (m : M) :
    a ^ k • Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) a k m = Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) a 0 m := by
  rw [← Presentations.Module.RestrictionTorsion.GradedModules.moduleFractionMap_scalar_apply]
  simpa only [zero_add] using Presentations.Module.Fractions.GradedModules.moduleFractionMap_raise (R := A) a 0 k m

theorem iteratedModuleFraction_common (a b : A) (i j : ℕ) (m : M) :
    Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) b (i + j)
      (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) a (i + j) (a ^ j • (b ^ i • m))) =
    Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) b j (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) a i m) := by
  rw [Presentations.Module.Fractions.GradedModules.moduleFractionMap_raise, Presentations.Module.RestrictionTorsion.GradedModules.moduleFractionMap_scalar_apply]
  rw [show i + j = j + i from add_comm i j, Presentations.Module.Fractions.GradedModules.moduleFractionMap_raise]

theorem iteratedModuleFraction_surj (a b : A) (x : Presentations.Module.Fractions.GradedModules.AwayModule b (Presentations.Module.Fractions.GradedModules.AwayModule a M)) :
    ∃ (k : ℕ) (m : M), Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) b k (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) a k m) = x := by
  obtain ⟨j, y, rfl⟩ := Presentations.Module.Fractions.GradedModules.moduleFractionMap_surj (R := A) b x
  obtain ⟨i, m, rfl⟩ := Presentations.Module.Fractions.GradedModules.moduleFractionMap_surj (R := A) a y
  exact ⟨i + j, a ^ j • (b ^ i • m), iteratedModuleFraction_common M a b i j m⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedModuleFractions.GradedModules
