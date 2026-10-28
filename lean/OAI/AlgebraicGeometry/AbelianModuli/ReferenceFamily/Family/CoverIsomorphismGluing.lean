import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.MappedCoverCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IndexedOverIsoGluing

/-! # Cover Isomorphism Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CoverIsomorphismGluing

noncomputable section

/-! Isomorphisms on the actual original affine cover glue after
base change when their two squares on each actual intersection commute.
Coverage is checked on both resulting scheme families. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem isoSquare_inverse {C : Type*} [Category C] {A B P Q : C}
    (e : A ≅ B) (f : P ≅ Q) (i : A ⟶ P) (j : B ⟶ Q)
    (h : i ≫ f.hom = e.hom ≫ j) : j ≫ f.inv = e.inv ≫ i := by
  apply (cancel_mono f.hom).mp
  simp only [Category.assoc, f.inv_hom_id, Category.comp_id]
  rw [h, ← Category.assoc, e.inv_hom_id, Category.id_comp]

variable (R : Type) [CommRing R] (X : Over (Spec (.of R))) [IsSeparated X.hom]
    (U : X.left.AffineOpenCover) {S : Scheme} (F G : Over (Spec (.of R)) ⥤ Over S)

attribute [local implicit_reducible] AffineCoverIntersections.familyCoverAffineOpen AffineCoverIntersections.familyCoverPairAffineOpen Affine.OpenDiagram.familyAffineOpenDiagram

structure FamilyCoverIsomorphisms where
  chart : ∀ i : U.I₀,
    F.obj ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj (AffineCoverIntersections.familyCoverAffineOpen R X U i)) ≅
      G.obj ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj (AffineCoverIntersections.familyCoverAffineOpen R X U i))
  pair : ∀ i j : U.I₀,
    F.obj ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j)) ≅
      G.obj ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j))
  left_square : ∀ i j : U.I₀,
    F.map (Affine.OpenDiagram.familyOpenMap X (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤
      (AffineCoverIntersections.familyCoverAffineOpen R X U i).1 from inf_le_left)) ≫ (chart i).hom =
    (pair i j).hom ≫ G.map (Affine.OpenDiagram.familyOpenMap X (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤
      (AffineCoverIntersections.familyCoverAffineOpen R X U i).1 from inf_le_left))
  right_square : ∀ i j : U.I₀,
    F.map (Affine.OpenDiagram.familyOpenMap X (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤
      (AffineCoverIntersections.familyCoverAffineOpen R X U j).1 from inf_le_right)) ≫ (chart j).hom =
    (pair i j).hom ≫ G.map (Affine.OpenDiagram.familyOpenMap X (show (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 ≤
      (AffineCoverIntersections.familyCoverAffineOpen R X U j).1 from inf_le_right))

namespace FamilyCoverIsomorphisms

variable {R X U F G} (D : FamilyCoverIsomorphisms R X U F G)

def symm : FamilyCoverIsomorphisms R X U G F where
  chart i := (D.chart i).symm
  pair i j := (D.pair i j).symm
  left_square i j := isoSquare_inverse (D.pair i j) (D.chart i) _ _ (D.left_square i j)
  right_square i j := isoSquare_inverse (D.pair i j) (D.chart j) _ _ (D.right_square i j)

theorem forward_compatible [PreservesLimitsOfShape WalkingCospan F] (i j : U.I₀) :
    pullback.fst (F.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U i).1)).left
        (F.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U j).1)).left ≫
        ((D.chart i).hom ≫ G.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U i).1)).left =
      pullback.snd _ _ ≫
        ((D.chart j).hom ≫ G.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U j).1)).left := by
  apply MappedCoverCompatibility.familyMappedCover_compatible R X U F (G.obj X)
    (fun i => (D.chart i).hom ≫ G.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U i).1))
  intro l m
  rw [← Category.assoc, D.left_square, Category.assoc, ← G.map_comp, Affine.OpenDiagram.familyOpenMap_inclusion,
    ← Category.assoc, D.right_square, Category.assoc, ← G.map_comp, Affine.OpenDiagram.familyOpenMap_inclusion]

def glue [PreservesLimitsOfShape WalkingCospan F] [PreservesLimitsOfShape WalkingCospan G]
    [∀ i : U.I₀, IsOpenImmersion (F.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U i).1)).left]
    [∀ i : U.I₀, IsOpenImmersion (G.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U i).1)).left]
    (hF : ∀ x : (F.obj X).left, ∃ i : U.I₀,
      x ∈ (F.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U i).1)).left.opensRange)
    (hG : ∀ x : (G.obj X).left, ∃ i : U.I₀,
      x ∈ (G.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U i).1)).left.opensRange) :
    F.obj X ≅ G.obj X :=
  IndexedOverIsoGluing.glueIndexedOverIso (F.obj X) (G.obj X)
    (fun i => F.obj ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj (AffineCoverIntersections.familyCoverAffineOpen R X U i)))
    (fun i => G.obj ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj (AffineCoverIntersections.familyCoverAffineOpen R X U i)))
    (fun i => F.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U i).1))
    (fun i => G.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (AffineCoverIntersections.familyCoverAffineOpen R X U i).1))
    hF hG D.chart D.forward_compatible D.symm.forward_compatible

end FamilyCoverIsomorphisms

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CoverIsomorphismGluing
