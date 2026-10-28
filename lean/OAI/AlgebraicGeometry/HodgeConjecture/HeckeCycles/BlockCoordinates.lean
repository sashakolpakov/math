import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupRetractPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PolarizedCartierRepresentative
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockRetraction

/-! # Block Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockCoordinates.CM

noncomputable section

/-! The original coefficient blocks have free prime-power coordinates
on geometric points and on scheme characters. These follow from the
actual integral projector retraction and the source polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupRetractPoints.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}

theorem points_coordinates (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (hordinary : Nat.card (A.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (n : ℕ) (τ : Gal(E/ℚ)) :
    ∃ r : ℕ, Nonempty ((Over.mk (𝟙 (Spec (.of k))) ⟶
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).X) ≃* TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) r) := by
  let T := Over.mk (𝟙 (Spec (.of k)))
  let B := (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).toGrp
  let Tor := PELModuli.CMPoints.BlockRetraction.actualTorsionGroup (q := q) A (n + 1)
  let : IsCommMonObj B.X := (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).comm
  let : IsCommMonObj Tor.X := A.torsionScheme_commutative (q ^ (n + 1))
  let inc := PELModuli.CMPoints.BlockRetraction.blockToTorsionGroup j iota hsplit A ρ (n + 1) τ
  let pr := PELModuli.CMPoints.BlockRetraction.torsionToBlockGroup j iota hsplit A ρ (n + 1) τ
  have h : inc ≫ pr = 𝟙 B := PELModuli.CMPoints.BlockRetraction.block_group_retraction j iota hsplit A ρ (n + 1) τ
  obtain ⟨c⟩ := Ordinary.TorsionCoordinates.CM.ordinary_torsion_coordinates A.scheme q g hordinary n
  let e : (T ⟶ Tor.X) ≃* TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g :=
    (((A.torsionSchemeYonedaIso (q ^ (n + 1))).app (.op T)).groupIsoToMulEquiv).trans c.symm
  exact IdempotentCoordinateGroup.CM.RetractCoordinates.exists_coordinates
    (Picard.PoincareBundle.Kernel.Scheme.pointsMap pr.hom.hom T) (Picard.PoincareBundle.Kernel.Scheme.pointsMap inc.hom.hom T) (GroupRetractPoints.CM.points_retraction inc pr h T)
    (q := q) (g := g) n e

theorem character_coordinates {N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hordinary : Nat.card (A.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (n : ℕ) (τ : Gal(E/ℚ)) :
    ∃ d : ℕ, Nonempty (((PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A.abelian ρ (n + 1) τ).toGrp ⟶
      AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))) ≃* TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) d) := by
  let B := (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A.abelian ρ (n + 1) τ).toGrp
  let inc := PELModuli.CMPoints.BlockRetraction.blockToTorsionGroup j iota hsplit A.abelian ρ (n + 1) τ
  let pr := PELModuli.CMPoints.BlockRetraction.torsionToBlockGroup j iota hsplit A.abelian ρ (n + 1) τ
  have h : inc ≫ pr = 𝟙 B := PELModuli.CMPoints.BlockRetraction.block_group_retraction j iota hsplit A.abelian ρ (n + 1) τ
  obtain ⟨e⟩ := PolarizedCartierRepresentative.CM.character_coordinates_all A q hordinary (n + 1)
  exact IdempotentCoordinateGroup.CM.RetractCoordinates.exists_coordinates (GroupRetractPoints.CM.precomposeCharacters inc) (GroupRetractPoints.CM.precomposeCharacters pr)
    (GroupRetractPoints.CM.characters_retraction inc pr h) (q := q) (g := g) n e.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockCoordinates.CM
