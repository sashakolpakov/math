import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalTorsionCharacters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CharacterCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionKernelGroupIso
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionCoordinates

/-! # Polarized Torsion Characters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PolarizedTorsionCharacters.CM

noncomputable section

/-! The source polarization and actual Cartier-Picard isomorphism
construct all characters of the original torsion scheme from dual torsion.
Ordinarity then supplies their standard prime-power coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalTorsionCharacters.Construction

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

def dualTorsionCharacters (m : ℕ) (hm : 0 < m)
    (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k))
      (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.abelian.scheme) ^ m)))) :
    A.dual.abelian.torsionPoints m (Over.mk (𝟙 (Spec (.of k)))) ≃*
      (@Grp.mk _ _ _ (A.abelian.torsionScheme m) (A.abelian.torsionScheme_group m) ⟶
        AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))) :=
  (((AbelianScheme.FrobeniusKernel.CanonicalTorsionCharacters.Construction.canonicalTorsionCartierPointIso A m hm C).app
    (.op (Over.mk (𝟙 (Spec (.of k)))))).groupIsoToMulEquiv.symm.trans
      (CharacterCoordinates.CM.representativePointsEquiv C)).trans
        (AbelianScheme.CartierDuality.CharacterMultiplicationMul.Construction.CharacterMultiplication.homCongrMulEquiv
          (TorsionKernelGroupIso.CM.kernelTorsionIso A.abelian m) (Iso.refl _))

theorem exists_character_coordinates (q : ℕ) [Fact q.Prime]
    (hordinary : Nat.card (A.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (n : ℕ)
    (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k))
      (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.abelian.scheme) ^ (q ^ (n + 1)))))) :
    Nonempty (TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g ≃*
      (@Grp.mk _ _ _ (A.abelian.torsionScheme (q ^ (n + 1)))
        (A.abelian.torsionScheme_group (q ^ (n + 1))) ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k)))) := by
  have ho := Picard.Homomorphisms.OrdinaryDivision.Construction.isogeny_preserves_ordinary_torsion_count A.abelian A.dual.abelian
    A.polarization.isogeny q (Fact.out : q.Prime) hordinary
  obtain ⟨e⟩ := Ordinary.TorsionCoordinates.CM.ordinary_torsion_coordinates
    A.dual.abelian.scheme q g ho n
  exact ⟨e.trans (dualTorsionCharacters A (q ^ (n + 1))
    (pow_pos (Fact.out : q.Prime).pos _) C)⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PolarizedTorsionCharacters.CM
