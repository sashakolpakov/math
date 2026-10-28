import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDComplexCoordinates

/-! # PD Point Symbols -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDPointSymbols

noncomputable section

/-! Literal symbol coordinates for the original algebra-action comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X)

abbrev hom_symbol (n : ℕ) (a : Q.thickening.ring) (v : Fin n → Q.thickening.ring) :=
  PD.DeRhamAlgebraCoordinates.iso_hom_symbol (WittVector p k) Q.thickening.ring
    (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers
    inferInstance (algebraMap (WittVector p k) Q.thickening.ring).toAlgebra
    toAlgebra_algebraMap.symm n a v

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDPointSymbols
