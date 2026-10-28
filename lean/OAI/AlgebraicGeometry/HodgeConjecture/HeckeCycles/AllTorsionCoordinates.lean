import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionCoordinates

/-! # All Torsion Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AllTorsionCoordinates.CM

noncomputable section

/-! Include level zero in the constructed ordinary torsion coordinates.
Its full torsion group is the identity group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion

def zeroCoordinates (A : Type*) [CommGroup A] (q g : ℕ) :
    TorsionCoordinateMaps.CM.Criterion.coordinates q 0 g ≃* AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ 0) := by
  let : Subsingleton (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ 0)) := ⟨fun x y => Subtype.ext (by
    have hx0 : x.val ^ (q ^ 0) = 1 := x.property
    have hy0 : y.val ^ (q ^ 0) = 1 := y.property
    have hx : x.val = 1 := by simpa only [pow_zero, pow_one] using hx0
    have hy : y.val = 1 := by simpa only [pow_zero, pow_one] using hy0
    exact hx.trans hy.symm)⟩
  let : Unique (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ 0)) := uniqueOfSubsingleton 1
  let : Subsingleton (TorsionCoordinateMaps.CM.Criterion.coordinates q 0 g) := by
    change Subsingleton (Multiplicative (Fin g → ZMod 1))
    infer_instance
  let : Unique (TorsionCoordinateMaps.CM.Criterion.coordinates q 0 g) := uniqueOfSubsingleton 1
  exact MulEquiv.ofUnique

variable {k : Type} [Field k] [IsAlgClosed k]
  (B : Over (Spec (.of k))) [GrpObj B] [IsCommMonObj B]
  [Smooth B.hom] [IsProper B.hom] [GeometricallyConnected B.hom]
  (q : ℕ) [Fact q.Prime] (g : ℕ)

theorem coordinates_all
    (hordinary : Nat.card (powMonoidHom q :
      (Over.mk (𝟙 (Spec (.of k))) ⟶ B) →* _).ker = q ^ g) (n : ℕ) :
    Nonempty (TorsionCoordinateMaps.CM.Criterion.coordinates q n g ≃*
      AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion (Over.mk (𝟙 (Spec (.of k))) ⟶ B) (q ^ n)) := by
  cases n with
  | zero => exact ⟨zeroCoordinates _ q g⟩
  | succ n => exact Ordinary.TorsionCoordinates.CM.ordinary_torsion_coordinates B q g hordinary n

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AllTorsionCoordinates.CM
