import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConeDiagramQuasiIso

/-! # Presheaf Map Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafMapQuasiIso

noncomputable section

/-! Pointwise quasi-isomorphisms on the actual affine nerve induce
a quasi-isomorphism on the original presheaf Čech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w
variable {C : Type v} [Category.{0} C] [HasBinaryProducts C]
  (R : Type u) [CommRing R] {ι : Type} [Finite ι] (U : ι → C)
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u w} R) ℕ} (f : K ⟶ L)
  (h : ∀ (j : ℕ) (b : Fin (j+1) → ι), QuasiIso
    ((((CategoryTheory.evaluation Cᵒᵖ (ModuleCat.{max u w} R)).obj
      (op (∏ᶜ (U ∘ b)))).mapHomologicalComplex (.up ℕ)).map f))

include h in
theorem quasiIso : QuasiIso ((GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)) := by
  apply ConeDiagramQuasiIso.quasiIso R U
  intro j b
  exact h j b

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafMapQuasiIso
