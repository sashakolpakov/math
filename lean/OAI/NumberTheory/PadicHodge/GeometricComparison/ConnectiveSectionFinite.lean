import OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveSectionCycle
import Mathlib.RingTheory.Noetherian.Basic

/-! # Connective Section Finite -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveSectionFinite.ConnectiveSectionFiniteness

noncomputable section

/-! Finite degree-zero sections bound the degree-zero derived sections of a connective complex. -/

open _root_.CategoryTheory Opposite

variable (R : Type) [CommRing R] [IsNoetherianRing R] (X : TopCat.{0})

local notation "V" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.Sheaves R X
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.coefficient R X

local instance : HasDerivedCategory.{1} V := HasDerivedCategory.standard _

theorem finite (K : CochainComplex V ℤ) [K.IsStrictlyGE 0]
    [Module.Finite R ((K.X 0).obj.obj (op ⊤))] :
    Module.Finite R ((DerivedCategory.singleFunctor V 0).obj A ⟶ DerivedCategory.Q.obj K) := by
  let P := ConnectiveSectionCycle.ConnectiveSectionKernel.sectionKernel R X K
  let : Module.Finite R P := Module.Finite.of_injective P.subtype Subtype.val_injective
  exact Module.Finite.equiv (ConnectiveSectionCycle.ConnectiveSectionKernel.equiv R X K).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveSectionFinite.ConnectiveSectionFiniteness
