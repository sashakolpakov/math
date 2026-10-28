import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero

/-! # All Degrees Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison

noncomputable section

/-! # The original acyclic-resolution comparison in every degree -/

open _root_.CategoryTheory

open _root_.CategoryTheory.Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C) (K : CochainComplex C ℕ) {Z : C}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))

def homologyIso (n : ℕ) : (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K).homology n ≅
    ModuleCat.of R (Ext.{z} X Z n) := by
  cases n with
  | zero => exact NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.homologyIso R X K ι
  | succ n => exact NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.positiveHomologyIso R X K ι hK n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison
