import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra
import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleWittLift

/-! # Global Function Witt -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionWitt

noncomputable section

/-! The actual Witt vectors of global regular functions form a finite free étale algebra over W(k). -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Finite k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] [Nonempty X.left]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X

include hprojective in
theorem free : Module.Free (WittVector p k) (WittVector p A) := by
  let := GlobalFunctionAlgebra.nontrivial k X
  let := GlobalFunctionAlgebra.module_finite k X hprojective
  let := GlobalFunctionAlgebra.etale k X p hprojective
  exact PeriodInvariants.FiniteEtaleWittModule.free p k A

include hprojective in
theorem finite : Module.Finite (WittVector p k) (WittVector p A) := by
  let := GlobalFunctionAlgebra.nontrivial k X
  let := GlobalFunctionAlgebra.module_finite k X hprojective
  let := GlobalFunctionAlgebra.etale k X p hprojective
  exact PeriodInvariants.FiniteEtaleWittModule.finite p k A

include hprojective in
theorem etale : Algebra.Etale (WittVector p k) (WittVector p A) := by
  let := GlobalFunctionAlgebra.nontrivial k X
  let := GlobalFunctionAlgebra.module_finite k X hprojective
  let := GlobalFunctionAlgebra.etale k X p hprojective
  exact PeriodInvariants.FiniteEtaleWittLift.etale p k A

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionWitt
