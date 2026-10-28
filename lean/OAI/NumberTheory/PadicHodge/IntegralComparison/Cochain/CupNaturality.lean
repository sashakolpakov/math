import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CohomologyCup

/-! # Cup Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CupNaturality.Cohomology

noncomputable section

/-! A morphism preserving products of actual cochains preserves the
induced products on the original categorical cohomology. -/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality

universe u v

variable {R : Type u} [CommRing R]
  {K L : CochainComplex (ModuleCat.{v} R) ℕ}
  (μ : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m))
  (ν : ∀ n m : ℕ, L.X n →ₗ[R] L.X m →ₗ[R] L.X (n + m))
  (hμ : ∀ n m (x : K.X n) (y : K.X m),
    K.d (n + m) (n + m + 1) (μ n m x y) =
      CohomologyCup.cupInto K μ (n + 1) m (n + m + 1) (by omega) (K.d n (n + 1) x) y +
        (-1 : ℤ) ^ n • CohomologyCup.cupInto K μ n (m + 1) (n + m + 1) (by omega) x (K.d m (m + 1) y))
  (hν : ∀ n m (x : L.X n) (y : L.X m),
    L.d (n + m) (n + m + 1) (ν n m x y) =
      CohomologyCup.cupInto L ν (n + 1) m (n + m + 1) (by omega) (L.d n (n + 1) x) y +
        (-1 : ℤ) ^ n • CohomologyCup.cupInto L ν n (m + 1) (n + m + 1) (by omega) x (L.d m (m + 1) y))
  (f : K ⟶ L)
  (hf : ∀ n m (x : K.X n) (y : K.X m),
    f.f (n + m) (μ n m x y) = ν n m (f.f n x) (f.f m y))

include hf in
theorem cycleMap_cup (p q : ℕ) (x : Module.CochainClasses.cycles K p) (y : Module.CochainClasses.cycles K q) :
    Module.CochainClassNaturality.cycleMap f (p + q) (CohomologyCup.cycleCup K μ hμ p q x y) =
      CohomologyCup.cycleCup L ν hν p q (Module.CochainClassNaturality.cycleMap f p x) (Module.CochainClassNaturality.cycleMap f q y) := by
  apply Subtype.ext
  exact hf p q x.val y.val

include hf in
theorem cohomologyMap_cup (p q : ℕ) (x : K.homology p) (y : K.homology q) :
    HomologicalComplex.homologyMap f (p + q) (CohomologyCup.cohomologyCup K μ hμ p q x y) =
      CohomologyCup.cohomologyCup L ν hν p q
        (HomologicalComplex.homologyMap f p x) (HomologicalComplex.homologyMap f q y) := by
  obtain ⟨x, rfl⟩ := Module.CochainClasses.classMap_surjective K p x
  obtain ⟨y, rfl⟩ := Module.CochainClasses.classMap_surjective K q y
  rw [CohomologyCup.cup_class, ← Module.CochainClassNaturality.naturality_apply, cycleMap_cup μ ν hμ hν f hf,
    ← CohomologyCup.cup_class, Module.CochainClassNaturality.naturality_apply, Module.CochainClassNaturality.naturality_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CupNaturality.Cohomology
