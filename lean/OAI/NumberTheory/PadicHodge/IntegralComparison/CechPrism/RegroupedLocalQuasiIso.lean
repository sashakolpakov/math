import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Regrouped
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.LocalQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConeDiagramQuasiIso

/-! # Regrouped Local Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.RegroupedLocalQuasiIso

noncomputable section

/-! Own-chart quasi-isomorphisms on the actual nerve imply that
the global-cone comparison is a quasi-isomorphism, through the proved
prism and the original row-total coordinate maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w
variable {C : Type v} [SemilatticeInf C]
  (R : Type u) [CommRing R] {ι : Type} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{max u w} R) ℕ)
  (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ CochainComplex (ModuleCat.{max u w} R) ℕ)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))
  (hγ : ∀ (j : ℕ) (b : Fin (j+1) → ι),
    QuasiIso ((γ.app (op (∏ᶜ (U ∘ b)))).app (op (∏ᶜ (U ∘ b)))))

include hγ in
theorem diagonal : QuasiIso (Regrouped.Comparison.diagonal R U Q B γ h) := by
  apply Cech.ConeDiagramQuasiIso.quasiIso R U (LocalAugmentation.map U Q B γ h)
  intro j b
  have : QuasiIso ((γ.app (op (∏ᶜ (U ∘ b)))).app (op (∏ᶜ (U ∘ b)))) := hγ j b
  exact LocalQuasiIso.quasiIso R U Q B γ h (∏ᶜ (U ∘ b)) (b 0)
    (leOfHom (Pi.π (U ∘ b) 0))

include h hγ in
theorem global : QuasiIso (Regrouped.Comparison.global R U Q B γ) := by
  exact Regrouped.Comparison.global_quasiIso R U Q B γ h
    (diagonal R U Q B γ h hγ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.RegroupedLocalQuasiIso
