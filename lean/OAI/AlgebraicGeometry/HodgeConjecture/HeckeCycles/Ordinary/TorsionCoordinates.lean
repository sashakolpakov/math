import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoordinateReduction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionCounts
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ElementaryCharacters

/-! # Torsion Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionCoordinates.CM

noncomputable section

/-! Ordinary geometric torsion has the standard coordinates at every
positive power level. The coordinates are constructed from the
first-level vector-space basis and actual division of points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionGenerators.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.FirstLevel

def firstStandardEquiv (q g : ℕ) :
    TorsionCoordinateMaps.CM.Criterion.coordinates q 1 g ≃* Multiplicative (Fin g → ZMod q) :=
  AddEquiv.toMultiplicative
    (AddEquiv.piCongrRight (fun _ : Fin g => (ZMod.ringEquivCongr (pow_one q)).toAddEquiv))

variable {A : Type*} [CommGroup A]

def firstCoordinateEquiv (q : ℕ) [Fact q.Prime] (g : ℕ)
    (hcard : Nat.card (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A q) = q ^ g) :
    TorsionCoordinateMaps.CM.Criterion.coordinates q 1 g ≃* AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A q := by
  let : Finite (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A q) :=
    Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero g (Fact.out : q.Prime).ne_zero)
  let e := Picard.Homomorphisms.ElementaryCharacters.Construction.elementaryCharacterGroupEquiv q (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A q) g
    (fun x => Subtype.ext x.property) hcard
  exact (firstStandardEquiv q g).trans (e.trans MulEquiv.ulift).symm

theorem exists_compatible_coordinates (q : ℕ) [Fact q.Prime] (g : ℕ)
    (hcard : Nat.card (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A q) = q ^ g)
    (hdiv : Function.Surjective (fun a : A => a ^ q)) (n : ℕ) :
    ∃ e : TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g ≃* AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ (n + 1)),
      ∀ i, TorsionCoordinateMaps.CM.FirstLevel.firstLevel q n (e (TorsionGenerators.CM.generator q (n + 1) g i)) =
        firstCoordinateEquiv q g hcard (TorsionGenerators.CM.generator q 1 g i) := by
  have hcount := TorsionCounts.CM.torsionTower_card q g hcard
    (fun m => TorsionCounts.CM.OrdinaryDivision.torsionTower_surjective_of_division q m hdiv)
    (n + 1)
  exact CoordinateReduction.CM.LiftedInjectivity.exists_coordinateEquiv q n g
    (Fact.out : q.Prime).pos hdiv (firstCoordinateEquiv q g hcard).toMonoidHom
    (firstCoordinateEquiv q g hcard).injective hcount

variable {k : Type} [Field k] [IsAlgClosed k]
  (B : Over (Spec (.of k))) [GrpObj B] [IsCommMonObj B]
  [Smooth B.hom] [IsProper B.hom] [GeometricallyConnected B.hom]
  (q : ℕ) [Fact q.Prime] (g : ℕ)

theorem ordinary_torsion_coordinates
    (hordinary : Nat.card (powMonoidHom q :
      (Over.mk (𝟙 (Spec (.of k))) ⟶ B) →* _).ker = q ^ g) (n : ℕ) :
    Nonempty (TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) g ≃*
      AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion (Over.mk (𝟙 (Spec (.of k))) ⟶ B) (q ^ (n + 1))) := by
  let : Finite (powMonoidHom q :
      (Over.mk (𝟙 (Spec (.of k))) ⟶ B) →* _).ker :=
    Nat.finite_of_card_ne_zero
      (hordinary ▸ pow_ne_zero g (Fact.out : q.Prime).ne_zero)
  obtain ⟨e, _⟩ := exists_compatible_coordinates q g hordinary
    (Picard.Homomorphisms.OrdinaryDivision.Construction.rational_points_divisible_of_finite_torsion B q) n
  exact ⟨e⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionCoordinates.CM
