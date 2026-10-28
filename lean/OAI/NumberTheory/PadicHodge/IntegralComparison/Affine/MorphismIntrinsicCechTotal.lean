import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.MorphismOrdinaryCechTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoverOrdinaryCech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechCoordinatePullback

/-! # Morphism Intrinsic Cech Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.MorphismIntrinsicCechTotal.Intrinsic

noncomputable section

/-! Ordinary affine coordinates identify the actual refined pullback
with pullback on the sheaf de Rham total, over an arbitrary base ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem paste {C : Type*} [Category* C] {A B D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ D) (s : D ⟶ E) (t : A ⟶ F)
    (c : F ⟶ E) (v : F ⟶ G) (d : G ⟶ H) (u : E ⟶ H)
    (h : a ≫ b ≫ s = t ≫ c) (k : v ≫ d = c ≫ u) :
    a ≫ b ≫ (s ≫ u) = (t ≫ v) ≫ d := by
  calc
    _ = (a ≫ b ≫ s) ≫ u := by simp only [Category.assoc]
    _ = (t ≫ c) ≫ u := congrArg (fun z => z ≫ u) h
    _ = t ≫ (v ≫ d) := by rw [Category.assoc, ← k]
    _ = _ := (Category.assoc _ _ _).symm

variable (R : Type) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))}
  [X.left.IsSeparated] [Y.left.IsSeparated]
  [IsProper X.hom] [Smooth X.hom] [IsProper Y.hom] [Smooth Y.hom]
  (f : X ⟶ Y) {ι κ : Type}
  (U : ι → AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts f.left) (V : κ → Y.left.affineOpens)
  (r : FormalCoproduct.mk ι ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target f.left).obj ∘ U) ⟶
    FormalCoproduct.mk κ V)
  (rX : ι → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index R X)
  (hX : ∀ i, ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source f.left).obj (U i)).val ≤
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X (rX i)).val)
  (rY : κ → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index R Y)
  (hY : ∀ i, (V i).val ≤ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R Y (rY i)).val)

def sourceCover := (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source f.left).obj ∘ U

def sourceOpens := (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left).obj ∘ sourceCover R f U

def targetOpens := (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion Y.left).obj ∘ V

def openRefinement := MorphismOrdinaryCechCoordinates.Ordinary.openRefinement R f U V r

omit [X.left.IsSeparated] [Y.left.IsSeparated] [IsProper X.hom] [Smooth X.hom] [IsProper Y.hom] [Smooth Y.hom] in
theorem coverLE (i : ι) : sourceOpens R f U i ≤
    f.left ⁻¹ᵁ targetOpens R V ((openRefinement R f U V r).f i) :=
  AlgebraicGeometry.Crystalline.Cohomology.SmallProjectedLE.SmallProjectedCechPullback.coverLE f.left
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.targetOpens R f)
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.sourceOpens R f)
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryPullback.AffineMorphismOrdinaryPullback.openMap R f) U (targetOpens R V)
    (openRefinement R f U V r) i

def bicomplexMap := AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.sheafMap R f
  (targetOpens R V) (sourceOpens R f U) (openRefinement R f U V r).f
  (coverLE R f U V r)

def map := HomologicalComplex₂.total.map (bicomplexMap R f U V r) (.up ℕ)

def sourceIso := MorphismOrdinaryCechTotal.Ordinary.sourceIso R f U ≪≫
  CoverDeRhamUnit.totalIso R X (sourceCover R f U) rX hX

def targetIso := MorphismOrdinaryCechTotal.Ordinary.targetIso R V ≪≫
  CoverDeRhamUnit.totalIso R Y V rY hY

theorem target_unit_hom :
    (CoverDeRhamUnit.totalIso R Y V rY hY).hom =
      HomologicalComplex₂.total.map
        (AlgebraicGeometry.Crystalline.Cohomology.Base.CoordinateCechUnit.BaseCoordinateCechUnit.map R Y (targetOpens R V)) (.up ℕ) := rfl

omit [Y.left.IsSeparated] [IsProper Y.hom] [Smooth Y.hom] in
theorem source_unit_hom :
    (CoverDeRhamUnit.totalIso R X (sourceCover R f U) rX hX).hom =
      HomologicalComplex₂.total.map
        (AlgebraicGeometry.Crystalline.Cohomology.Base.CoordinateCechUnit.BaseCoordinateCechUnit.map R X (sourceOpens R f U)) (.up ℕ) := rfl

omit [X.left.IsSeparated] [Y.left.IsSeparated] [IsProper X.hom] [Smooth X.hom] [IsProper Y.hom] [Smooth Y.hom] in
theorem coordinate_map : MorphismOrdinaryCechTotal.Ordinary.directMap R f U V r =
    HomologicalComplex₂.total.map
      (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.coordinateMap R f
        (targetOpens R V) (sourceOpens R f U) (openRefinement R f U V r).f
        (coverLE R f U V r)) (.up ℕ) := rfl

theorem unit_square :
    (CoverDeRhamUnit.totalIso R Y V rY hY).hom ≫ Intrinsic.map R f U V r =
      MorphismOrdinaryCechTotal.Ordinary.directMap R f U V r ≫
        (CoverDeRhamUnit.totalIso R X (sourceCover R f U) rX hX).hom := by
  have h := congrArg
    (fun a => HomologicalComplex₂.total.map a (.up ℕ))
    (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.unit_square R f
      (targetOpens R V) (sourceOpens R f U) (openRefinement R f U V r).f
      (coverLE R f U V r))
  simp only [HomologicalComplex₂.total.map_comp] at h
  rw [target_unit_hom, source_unit_hom, coordinate_map]
  exact h

theorem total :
    MorphismOrdinaryCechTotal.Ordinary.refinement R f U V r ≫
      MorphismOrdinaryCechTotal.Ordinary.geometricMap R f U ≫
        (sourceIso R f U rX hX).hom =
    (targetIso R V rY hY).hom ≫ Intrinsic.map R f U V r :=
  paste
    (MorphismOrdinaryCechTotal.Ordinary.refinement R f U V r)
    (MorphismOrdinaryCechTotal.Ordinary.geometricMap R f U)
    (MorphismOrdinaryCechTotal.Ordinary.sourceIso R f U).hom
    (MorphismOrdinaryCechTotal.Ordinary.targetIso R V).hom
    (MorphismOrdinaryCechTotal.Ordinary.directMap R f U V r)
    (CoverDeRhamUnit.totalIso R Y V rY hY).hom
    (Intrinsic.map R f U V r)
    (CoverDeRhamUnit.totalIso R X (sourceCover R f U) rX hX).hom
    (MorphismOrdinaryCechTotal.Ordinary.total R f U V r)
    (unit_square R f U V r rX hX rY hY)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.MorphismIntrinsicCechTotal.Intrinsic
