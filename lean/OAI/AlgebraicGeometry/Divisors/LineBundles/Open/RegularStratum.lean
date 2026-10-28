import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.StratumIso

/-! # Regular Stratum -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RegularStratum.BundleCycles

noncomputable section

/-! Open immersions preserve the actual smooth stratum by a genuine
restriction map and a cartesian square of schemes over the complex base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductOver.Constructions

theorem schemeSmoothLocus_eq {A B : Scheme.{0}} (f g : A ⟶ B)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) :
    f.smoothLocus = g.smoothLocus := by
  subst g
  rfl

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFinitePresentation X.hom]
    [LocallyOfFinitePresentation Y.hom] (i : X ⟶ Y) [IsOpenImmersion i.left]

theorem openRegularStratum_preimage : i.left ⁻¹ᵁ Y.hom.smoothLocus = X.hom.smoothLocus := by
  have h := Scheme.Hom.preimage_smoothLocus_eq i.left Y.hom
  exact h.trans (schemeSmoothLocus_eq _ _ i.w)

def openRegularStratumMap : CycleClass.Geometric.SmoothStratum.smoothStratum X.hom ⟶ CycleClass.Geometric.SmoothStratum.smoothStratum Y.hom :=
  i.left.resLE Y.hom.smoothLocus X.hom.smoothLocus (openRegularStratum_preimage i).symm.le

theorem openRegularStratumMap_inclusion :
    openRegularStratumMap i ≫ CycleClass.Geometric.SmoothStratum.smoothStratumι Y.hom = CycleClass.Geometric.SmoothStratum.smoothStratumι X.hom ≫ i.left :=
  Scheme.Hom.resLE_comp_ι _ _

instance openRegularStratumMap_isOpenImmersion : IsOpenImmersion (openRegularStratumMap i) := by
  have h : IsOpenImmersion (openRegularStratumMap i ≫ CycleClass.Geometric.SmoothStratum.smoothStratumι Y.hom) :=
    (congrArg (fun f => IsOpenImmersion f) (openRegularStratumMap_inclusion i)).mpr inferInstance
  exact IsOpenImmersion.of_comp (openRegularStratumMap i) (CycleClass.Geometric.SmoothStratum.smoothStratumι Y.hom)

def openRegularStratumOverMap : CycleClass.Thom.Regular.ProductOver.Constructions.regularOver X ⟶ CycleClass.Thom.Regular.ProductOver.Constructions.regularOver Y :=
  Over.homMk (openRegularStratumMap i) (by
    change openRegularStratumMap i ≫ (CycleClass.Geometric.SmoothStratum.smoothStratumι Y.hom ≫ Y.hom) = CycleClass.Geometric.SmoothStratum.smoothStratumι X.hom ≫ X.hom
    rw [← Category.assoc, openRegularStratumMap_inclusion, Category.assoc, i.w])

theorem openRegularStratumOverMap_inclusion :
    openRegularStratumOverMap i ≫ CycleClass.Thom.Regular.ProductOver.Constructions.regularOverInclusion Y = CycleClass.Thom.Regular.ProductOver.Constructions.regularOverInclusion X ≫ i :=
  Over.OverMorphism.ext (openRegularStratumMap_inclusion i)

theorem openRegularStratum_isPullback :
    IsPullback (openRegularStratumMap i) (CycleClass.Geometric.SmoothStratum.smoothStratumι X.hom) (CycleClass.Geometric.SmoothStratum.smoothStratumι Y.hom) i.left := by
  apply IsOpenImmersion.isPullback
  · exact (openRegularStratumMap_inclusion i).symm
  · change i.left ⁻¹ᵁ Y.hom.smoothLocus.ι.opensRange = X.hom.smoothLocus.ι.opensRange
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, openRegularStratum_preimage]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RegularStratum.BundleCycles
