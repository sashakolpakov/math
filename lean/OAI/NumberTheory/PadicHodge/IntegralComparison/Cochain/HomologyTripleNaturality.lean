import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycleMaps

/-! # Homology Triple Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomologyTripleNaturality

noncomputable section

/-!
# IntegralComparison: the natural homology identification with three consecutive cochain terms
-/

open _root_.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℕ} (φ : K ⟶ L) (n : ℕ)

theorem naturality : HomologicalComplex.homologyMap φ (n + 1) ≫
    (L.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom =
      (K.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom ≫
        ShortComplex.homologyMap (Augmented.ResolutionCycleMaps.differential φ n) := by
  let H := ShortComplex.homologyFunctor C
  have h := (HomologicalComplex.natIsoSc' C (ComplexShape.up ℕ) n (n + 1) (n + 2)
    (by simp) (by simp)).hom.naturality φ
  exact (H.map_comp _ _).symm.trans ((congrArg H.map h).trans (H.map_comp _ _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomologyTripleNaturality
