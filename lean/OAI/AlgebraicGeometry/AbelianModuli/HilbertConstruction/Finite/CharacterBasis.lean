import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Character Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CharacterBasis

noncomputable section

/-! Characters form an explicit basis of functions on a finite abelian group over a field containing the required roots of unity. -/
universe u v
variable (K : Type u) [Field K] (G : Type v) [CommGroup G]

theorem finiteAbelianCharacter_linearIndependent :
    LinearIndependent K (fun χ : G →* Kˣ => fun g : G => (χ g : K)) := by
  exact (linearIndependent_monoidHom G K).comp
    (fun χ : G →* Kˣ => (Units.coeHom K).comp χ) (by
      intro χ ψ h
      apply MonoidHom.ext
      intro g
      apply Units.ext
      exact DFunLike.congr_fun h g)

variable [Fintype G] [HasEnoughRootsOfUnity K (Monoid.exponent G)]

def finiteAbelianCharacterBasis : Module.Basis (G →* Kˣ) K (G → K) := by
  classical
  let : Fintype (G →* Kˣ) := Fintype.ofFinite _
  exact basisOfLinearIndependentOfCardEqFinrank (finiteAbelianCharacter_linearIndependent K G) (by
    simpa only [Nat.card_eq_fintype_card, Module.finrank_fintype_fun_eq_card] using
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G K)

@[simp]
theorem finiteAbelianCharacterBasis_apply (χ : G →* Kˣ) (g : G) :
    finiteAbelianCharacterBasis K G χ g = (χ g : K) := by
  classical
  simp only [finiteAbelianCharacterBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CharacterBasis
