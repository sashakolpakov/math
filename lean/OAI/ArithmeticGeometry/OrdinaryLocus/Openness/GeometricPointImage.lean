import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PointDistinct

/-! # Geometric Point Image -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricPointImage.Construction

noncomputable section

/-! Geometric points and the image of a morphism in the Openness argument. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

/-- A locally finite-type scheme has a geometric point over `s` exactly
when `s` is in its underlying image. -/
theorem nonempty_geometricPoints_iff_mem_range
    {S : Scheme} (A : Over S) [LocallyOfFiniteType A.hom] (s : S) :
    Nonempty (DefinitionsTorsion.geometricPoint S s ⟶ A) ↔ s ∈ Set.range A.hom := by
  let t : (DefinitionsTorsion.geometricPoint S s).left :=
    IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))
  constructor
  · rintro ⟨h⟩
    refine ⟨h.left t, ?_⟩
    change (h.left ≫ A.hom) t = s
    rw [h.w]
    exact S.fromSpecResidueField_apply s _
  · rintro ⟨x, hx⟩
    have hxt : A.hom x = (DefinitionsTorsion.geometricPoint S s).hom t :=
      hx.trans (S.fromSpecResidueField_apply s _).symm
    obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback x t hxt
    have : Nonempty (DefinitionsTorsion.Construction.geometricFiberScheme A s) := ⟨z⟩
    have : JacobsonSpace (DefinitionsTorsion.geometricPoint S s).left := by
      change JacobsonSpace (Spec (.of (AlgebraicClosure (S.residueField s))))
      infer_instance
    have : JacobsonSpace (DefinitionsTorsion.Construction.geometricFiberScheme A s) :=
      LocallyOfFiniteType.jacobsonSpace (DefinitionsTorsion.Construction.geometricFiberMap A s)
    obtain ⟨c, _, hc⟩ := nonempty_inter_closedPoints
      (X := DefinitionsTorsion.Construction.geometricFiberScheme A s) Set.univ_nonempty isOpen_univ.isLocallyClosed
    exact ⟨(DefinitionsTorsion.Construction.geometricClosedPointEquiv A s).symm ⟨c, hc⟩⟩

/-- For an open, locally finite-type family, existence of a geometric
point is an open condition on the base. -/
theorem isOpen_nonempty_geometricPoints
    {S : Scheme} (A : Over S) [LocallyOfFiniteType A.hom] [UniversallyOpen A.hom] :
    IsOpen {s : S | Nonempty (DefinitionsTorsion.geometricPoint S s ⟶ A)} := by
  have heq : {s : S | Nonempty (DefinitionsTorsion.geometricPoint S s ⟶ A)} = Set.range A.hom := by
    ext s
    exact nonempty_geometricPoints_iff_mem_range A s
  rw [heq]
  exact A.hom.isOpenMap.isOpen_range

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricPointImage.Construction
