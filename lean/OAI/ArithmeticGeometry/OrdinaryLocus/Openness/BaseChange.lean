import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # Base Change -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseChange.Construction

noncomputable section

/-! Base change of the actual torsion scheme in Openness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S T : Scheme} (f : T ⟶ S) (A : Over S) [GrpObj A]

/-- Base change preserves the kernel of multiplication by n. -/
def torsionBaseChangeIso (n : ℕ) :
    (Over.pullback f).obj (DefinitionsTorsion.Construction.torsionScheme A n) ≅
      DefinitionsTorsion.Construction.torsionScheme ((Over.pullback f).obj A) n := by
  let F := Over.pullback f
  have hp : F.map ((𝟙 A) ^ n) = (𝟙 (F.obj A)) ^ n := by
    exact ((F.homMonoidHom (X := A) (M := A)).map_pow (𝟙 A) n).trans
      (congrArg (fun k => k ^ n) (F.map_id A))
  have h1 : F.map (1 : A ⟶ A) = 1 := F.map_one
  exact (PreservesEqualizer.iso F ((𝟙 A) ^ n) (1 : A ⟶ A)) ≪≫
    eqToIso (by rw [hp, h1]; rfl)

/-- Finiteness can be transported across an isomorphism of S-schemes. -/
theorem isFinite_of_overIso {B C : Over S} (e : B ≅ C) [IsFinite B.hom] :
    IsFinite C.hom := by
  have : IsIso e.inv.left := (Over.forget S).map_isIso e.inv
  rw [← e.inv.w]
  infer_instance

/-- A finite torsion kernel remains finite after any base change. -/
theorem isFinite_torsion_baseChange (n : ℕ) [IsFinite (DefinitionsTorsion.Construction.torsionScheme A n).hom] :
    IsFinite (DefinitionsTorsion.Construction.torsionScheme ((Over.pullback f).obj A) n).hom := by
  have : IsFinite ((Over.pullback f).obj (DefinitionsTorsion.Construction.torsionScheme A n)).hom := by
    change IsFinite (pullback.snd (DefinitionsTorsion.Construction.torsionScheme A n).hom f)
    infer_instance
  exact isFinite_of_overIso (torsionBaseChangeIso f A n)

/-- The finite restriction supplied by the geometric-fiber argument is
the finite torsion scheme of the base-changed group. -/
theorem isFinite_torsion_openRestriction (n : ℕ) (U : S.Opens)
    [IsFinite ((DefinitionsTorsion.Construction.torsionScheme A n).hom ∣_ U)] :
    IsFinite (DefinitionsTorsion.Construction.torsionScheme ((Over.pullback U.ι).obj A) n).hom := by
  have : IsFinite ((Over.pullback U.ι).obj (DefinitionsTorsion.Construction.torsionScheme A n)).hom := by
    change IsFinite (pullback.snd (DefinitionsTorsion.Construction.torsionScheme A n).hom U.ι)
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  exact isFinite_of_overIso (torsionBaseChangeIso U.ι A n)

/-- Near an ordinary point, multiplication by p is finite on the
base-changed proper group scheme. -/
theorem exists_finite_multiplication_neighborhood
    [IsProper A.hom] [IsCommMonObj A]
    (p : ℕ) [Fact p.Prime] (s : S) (hs : DefinitionsTorsion.IsOrdinaryAt p A s) :
    ∃ U : S.Opens, s ∈ U ∧
      IsFinite (Multiplication.Construction.multiplicationMap ((Over.pullback U.ι).obj A) p).left := by
  obtain ⟨U, hsU, hU⟩ := DefinitionsTorsion.Construction.exists_finite_torsion_neighborhood s A p hs
  have : IsFinite ((DefinitionsTorsion.Construction.torsionScheme A p).hom ∣_ U) := hU
  have : IsFinite (DefinitionsTorsion.Construction.torsionScheme ((Over.pullback U.ι).obj A) p).hom :=
    isFinite_torsion_openRestriction A p U
  have : IsProper ((Over.pullback U.ι).obj A).hom := by
    change IsProper (pullback.snd A.hom U.ι)
    infer_instance
  exact ⟨U, hsU, Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion
    ((Over.pullback U.ι).obj A) p⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseChange.Construction
