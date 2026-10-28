import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PolarizedTorsionCharacters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AllTorsionCoordinates
import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

/-! # Polarized Cartier Representative -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PolarizedCartierRepresentative.CM

noncomputable section

/-! The original polarization constructs a finite Cartier representative
for every positive multiplication kernel. No representative is an input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion.Construction

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

def representative (m : ℕ) (hm : 0 < m) :
    AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k))
      (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.abelian.scheme) ^ m))) := by
  obtain ⟨hf, hflat, _, hfp⟩ := AbelianScheme.FrobeniusKernel.CanonicalTorsionCartierIso.Construction.polarized_positiveMultiplication_cover A m hm
  have hK := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree ((𝟙 A.abelian.scheme) ^ m) ⟨hf, hflat, hfp⟩
  let : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.abelian.scheme) ^ m)).hom := hK.1
  let : Flat (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.abelian.scheme) ^ m)).hom := hK.2.1
  let : LocallyOfFinitePresentation (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.abelian.scheme) ^ m)).hom := hK.2.2
  exact CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation (Spec (.of k))
    (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.abelian.scheme) ^ m)))

theorem exists_character_coordinates (q : ℕ) [Fact q.Prime]
    (hordinary : Nat.card (A.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (n : ℕ) :
    Nonempty (TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g ≃*
      (@Grp.mk _ _ _ (A.abelian.torsionScheme (q ^ (n + 1)))
        (A.abelian.torsionScheme_group (q ^ (n + 1))) ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k)))) :=
  PolarizedTorsionCharacters.CM.exists_character_coordinates A q hordinary n
    (representative A (q ^ (n + 1)) (pow_pos (Fact.out : q.Prime).pos _))

theorem character_coordinates_all (q : ℕ) [Fact q.Prime]
    (hordinary : Nat.card (A.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (n : ℕ) :
    Nonempty (TorsionCoordinateMaps.CM.Criterion.coordinates q n g ≃*
      (@Grp.mk _ _ _ (A.abelian.torsionScheme (q ^ n))
        (A.abelian.torsionScheme_group (q ^ n)) ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k)))) := by
  have ho := Picard.Homomorphisms.OrdinaryDivision.Construction.isogeny_preserves_ordinary_torsion_count A.abelian A.dual.abelian
    A.polarization.isogeny q (Fact.out : q.Prime) hordinary
  obtain ⟨e⟩ := AllTorsionCoordinates.CM.coordinates_all A.dual.abelian.scheme q g ho n
  let hm := pow_pos (Fact.out : q.Prime).pos n
  exact ⟨e.trans (PolarizedTorsionCharacters.CM.dualTorsionCharacters A (q ^ n) hm
    (representative A (q ^ n) hm))⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PolarizedCartierRepresentative.CM
