import OAI.NumberTheory.PadicHodge.PeriodInvariants.ExteriorSemilinearBaseChange

/-! # Exterior Base -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorBase.ExteriorBaseChangeWords

noncomputable section

/-! # Exterior scalar change on coordinate words -/

universe u

variable {R S σ : Type u} [CommRing R] [CommRing S] [LinearOrder σ] (φ : R →+* S)

theorem word (n : ℕ) (v : Fin n → σ) :
    NumberTheory.PadicHodge.PeriodInvariants.ExteriorSemilinearBaseChange.exteriorMap φ n
      (exteriorPower.ιMulti R n (fun j => Finsupp.single (v j) 1)) =
        exteriorPower.ιMulti S n (fun j => Finsupp.single (v j) 1) := by
  apply (NumberTheory.PadicHodge.PeriodInvariants.EquivariantKoszul.exteriorBasis (R := S) (σ := σ) n).repr.injective
  apply Finsupp.ext
  intro s
  rw [NumberTheory.PadicHodge.PeriodInvariants.ExteriorSemilinearBaseChange.exteriorMap_repr]
  exact NumberTheory.PadicHodge.PeriodInvariants.ExteriorWedgeBaseChange.basis_word_map φ n v s

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorBase.ExteriorBaseChangeWords
