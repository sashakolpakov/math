import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionZero

/-! # Resolution Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionCohomology

noncomputable section

/-! An augmented source resolution acyclic for the original coefficient sheaf computes actual Ext in every degree. -/

open _root_.CategoryTheory Opposite

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C)
  (K : CochainComplex Cᵒᵖ ℕ) {Z : Cᵒᵖ} (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K) [QuasiIso ι]
  (hK : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y (q + 1)))

def homologyIso (i : ℕ) : (Resolution.Comparison.complex R Y K).homology i ≅
    ModuleCat.of R (Ext.{z} Z.unop Y i) := by
  cases i with
  | zero => exact ResolutionZero.homologyIso R Y K ι
  | succ i => exact Resolution.Comparison.positiveHomologyIso R Y K ι hK i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionCohomology
