import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseChange
import Mathlib.CategoryTheory.Conj

/-! # Open Base Change -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenBaseChange.Construction

noncomputable section

/-! Geometric points and torsion counts after restricting the base to an open subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

/-- The geometric point of an open subscheme is isomorphic, over the original
base, to the geometric point specified at its image. -/
def geometricPointOpenIso
    {S T : Scheme} (i : T ⟶ S) [IsOpenImmersion i] (t : T) :
    (Over.map i).obj (DefinitionsTorsion.geometricPoint T t) ≅ DefinitionsTorsion.geometricPoint S (i t) := by
  let e₀ := (asIso (i.residueFieldMap t)).commRingCatIsoToRingEquiv
  let e := IsAlgClosure.equivOfEquiv
    (AlgebraicClosure (S.residueField (i t))) (AlgebraicClosure (T.residueField t)) e₀
  refine Over.isoMk (Scheme.Spec.mapIso e.toCommRingCatIso.op) ?_
  have he : CommRingCat.ofHom (algebraMap (S.residueField (i t))
      (AlgebraicClosure (S.residueField (i t)))) ≫ CommRingCat.ofHom e.toRingHom =
      i.residueFieldMap t ≫ CommRingCat.ofHom
        (algebraMap (T.residueField t) (AlgebraicClosure (T.residueField t))) := by
    ext x
    exact IsAlgClosure.equivOfEquiv_algebraMap _ _ e₀ x
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField (i t))
        (AlgebraicClosure (S.residueField (i t))))) ≫ S.fromSpecResidueField (i t)) =
      (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t)
        (AlgebraicClosure (T.residueField t)))) ≫ T.fromSpecResidueField t) ≫ i
  have he' : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField (i t))
        (AlgebraicClosure (S.residueField (i t))))) =
      Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t)
        (AlgebraicClosure (T.residueField t)))) ≫ Spec.map (i.residueFieldMap t) :=
    (Spec.map_comp _ _).symm.trans ((congrArg Spec.map he).trans (Spec.map_comp _ _))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ S.fromSpecResidueField (i t)) he').trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a => Spec.map (CommRingCat.ofHom
          (algebraMap (T.residueField t) (AlgebraicClosure (T.residueField t)))) ≫ a)
          (i.SpecMap_residueFieldMap_fromSpecResidueField t)).trans
          (Category.assoc _ _ _).symm)))

/-- Geometric points of a base restriction are the original geometric points. -/
def geometricPointsOpenEquiv
    {S T : Scheme} (i : T ⟶ S) [IsOpenImmersion i] (A : Over S) (t : T) :
    (DefinitionsTorsion.geometricPoint T t ⟶ (Over.pullback i).obj A) ≃
      (DefinitionsTorsion.geometricPoint S (i t) ⟶ A) :=
  ((Over.mapPullbackAdj i).homEquiv (DefinitionsTorsion.geometricPoint T t) A).symm.trans
    (Iso.homCongr (geometricPointOpenIso i t) (Iso.refl A))

theorem geometricPointCard_openBaseChange
    {S T : Scheme} (i : T ⟶ S) [IsOpenImmersion i] (A : Over S) (t : T) :
    Nat.card (DefinitionsTorsion.geometricPoint T t ⟶ (Over.pullback i).obj A) =
      Nat.card (DefinitionsTorsion.geometricPoint S (i t) ⟶ A) :=
  Nat.card_congr (geometricPointsOpenEquiv i A t)

/-- Actual geometric torsion cardinality is unchanged by restricting the base. -/
theorem torsionPointCard_openBaseChange
    {S T : Scheme} (i : T ⟶ S) [IsOpenImmersion i] (A : Over S) [GrpObj A]
    (n : ℕ) (t : T) :
    Nat.card {x : DefinitionsTorsion.geometricPoint T t ⟶ (Over.pullback i).obj A // x ^ n = 1} =
      Nat.card {x : DefinitionsTorsion.geometricPoint S (i t) ⟶ A // x ^ n = 1} := by
  rw [← DefinitionsTorsion.Construction.geometric_torsion_card, ← DefinitionsTorsion.Construction.geometric_torsion_card]
  have h := Nat.card_congr (Iso.homCongr (Iso.refl (DefinitionsTorsion.geometricPoint T t))
    (BaseChange.Construction.torsionBaseChangeIso i A n))
  exact h.symm.trans (geometricPointCard_openBaseChange i (DefinitionsTorsion.Construction.torsionScheme A n) t)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenBaseChange.Construction
