import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationFlat
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricPointCount

/-! # Finite Flat Neighborhood -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatNeighborhood.Construction

noncomputable section

/-! Finite flat torsion near an ordinary point in Openness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

/-- Near an ordinary point, the torsion scheme is finite, flat, and
locally of finite presentation over the base. -/
theorem exists_finite_flat_torsion_neighborhood
    (p : ℕ) [Fact p.Prime] (s : S) (hs : DefinitionsTorsion.IsOrdinaryAt p A s) :
    ∃ U : S.Opens, s ∈ U ∧ IsFinite ((DefinitionsTorsion.Construction.torsionScheme A p).hom ∣_ U) ∧
      Flat ((DefinitionsTorsion.Construction.torsionScheme A p).hom ∣_ U) ∧
      LocallyOfFinitePresentation ((DefinitionsTorsion.Construction.torsionScheme A p).hom ∣_ U) := by
  obtain ⟨U, hsU, hfin⟩ := DefinitionsTorsion.Construction.exists_finite_torsion_neighborhood s A p hs
  have : IsFinite ((DefinitionsTorsion.Construction.torsionScheme A p).hom ∣_ U) := hfin
  let B := (Over.pullback U.ι).obj A
  have : Smooth B.hom := by change Smooth (pullback.snd A.hom U.ι); infer_instance
  have : IsProper B.hom := by change IsProper (pullback.snd A.hom U.ι); infer_instance
  have : GeometricallyConnected B.hom := by
    change GeometricallyConnected (pullback.snd A.hom U.ι)
    infer_instance
  have : IsFinite (DefinitionsTorsion.Construction.torsionScheme B p).hom := BaseChange.Construction.isFinite_torsion_openRestriction A p U
  have : Flat (DefinitionsTorsion.Construction.torsionScheme B p).hom := MultiplicationFlat.Construction.flat_torsion_of_isFinite B p
  have hpb : Flat ((Over.pullback U.ι).obj (DefinitionsTorsion.Construction.torsionScheme A p)).hom :=
    RelativeBaseChange.Construction.flat_of_overIso (BaseChange.Construction.torsionBaseChangeIso U.ι A p)
  have : Flat (pullback.snd (DefinitionsTorsion.Construction.torsionScheme A p).hom U.ι) := hpb
  have hflat : Flat ((DefinitionsTorsion.Construction.torsionScheme A p).hom ∣_ U) := by
    rw [morphismRestrict]
    infer_instance
  have : LocallyOfFinitePresentation (DefinitionsTorsion.Construction.torsionScheme A p).hom :=
    FinitePresentation.Construction.locallyOfFinitePresentation_torsion A p
  exact ⟨U, hsU, hfin, hflat, inferInstance⟩

/-- When the torsion kernel is finite, its actual geometric torsion-point
count is lower semicontinuous under the hypotheses of Openness. -/
theorem lowerSemicontinuous_torsionPointCard_of_isFinite (n : ℕ)
    [IsFinite (DefinitionsTorsion.Construction.torsionScheme A n).hom] :
    LowerSemicontinuous
      (fun s : S => Nat.card {x : DefinitionsTorsion.geometricPoint S s ⟶ A // x ^ n = 1}) := by
  have : Flat (DefinitionsTorsion.Construction.torsionScheme A n).hom := MultiplicationFlat.Construction.flat_torsion_of_isFinite A n
  have : LocallyOfFinitePresentation (DefinitionsTorsion.Construction.torsionScheme A n).hom :=
    FinitePresentation.Construction.locallyOfFinitePresentation_torsion A n
  simpa only [DefinitionsTorsion.Construction.geometric_torsion_card] using
    GeometricPointCount.Construction.lowerSemicontinuous_finite_geometricPointCard (DefinitionsTorsion.Construction.torsionScheme A n)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatNeighborhood.Construction
