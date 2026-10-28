import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.GluingNormalization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechObjectChange

/-! # Open Invariant -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.OpenInvariant

noncomputable section

/-!
# The actual invariant of ordinary descent commutes with open restriction
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.OverlapPullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing

variable {X Y Z X' Y' Z' : Scheme.{u}}
  (f : X ⟶ Y) (p q : Z ⟶ X) (h : p ≫ f = q ≫ f)
  (f' : X' ⟶ Y') (p' q' : Z' ⟶ X') (h' : p' ≫ f' = q' ≫ f')
  (iY : Y' ⟶ Y) (iX : X' ⟶ X) (iZ : Z' ⟶ Z)
  [IsOpenImmersion iY] [IsOpenImmersion iX] [IsOpenImmersion iZ]
  (hf : iX ≫ f = f' ≫ iY) (hp : iZ ≫ p = p' ≫ iX) (hq : iZ ≫ q = q' ≫ iX)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))

include hf hq in
omit [IsOpenImmersion iY] [IsOpenImmersion iX] [IsOpenImmersion iZ] in
/-- The maps of the restricted ordinary overlap commute with the map of bases. -/
theorem base_square : iZ ≫ (q ≫ f) = (q' ≫ f') ≫ iY := by
  rw [← Category.assoc, hq, Category.assoc, hf, ← Category.assoc]

omit [IsOpenImmersion iY] [IsOpenImmersion iX] [IsOpenImmersion iZ] in
/-- The ordinary gluing after restricting the cover is exactly the transported geometric gluing. -/
theorem pulledGluing_eq :
    Open.GluingNormalization.pullbackGluing p q p' q' iX iZ hp hq (D.obj PUnit.unit)
      (OverlapPullback.overlapIso f D (q ≫ f) p q h rfl) =
    OverlapPullback.overlapIso f' (SquareGluing.pulledDatum f f' iX iY hf D) (q' ≫ f') p' q' h' rfl :=
  SquareGluing.squareGluing_eq f f' iX iY hf D (q ≫ f) p q h rfl (q' ≫ f') p' q' h' rfl iZ
    (base_square f q f' q' iY iX iZ hf hq) hp hq

omit [IsOpenImmersion iY] in
/-- The actual restriction-to-pullback isomorphism is compatible with ordinary descent gluing. -/
theorem gluing_compatible :
    (Scheme.Modules.pullback p').map ((Scheme.Modules.restrictFunctorIsoPullback iX).app
      (D.obj PUnit.unit)).hom ≫
      (OverlapPullback.overlapIso f' (SquareGluing.pulledDatum f f' iX iY hf D) (q' ≫ f') p' q' h' rfl).hom =
    (Open.CechInvariant.gluing p q p' q' iX iZ hp hq (D.obj PUnit.unit)
      (OverlapPullback.overlapIso f D (q ≫ f) p q h rfl)).hom ≫
      (Scheme.Modules.pullback q').map ((Scheme.Modules.restrictFunctorIsoPullback iX).app
        (D.obj PUnit.unit)).hom := by
  rw [← pulledGluing_eq f p q h f' p' q' h' iY iX iZ hf hp hq D]
  exact Open.GluingNormalization.compatible p q p' q' iX iZ hp hq (D.obj PUnit.unit)
    (OverlapPullback.overlapIso f D (q ≫ f) p q h rfl)

variable (hfpre : f ⁻¹ᵁ iY.opensRange ≤ iX.opensRange)
  (hqpre : q ⁻¹ᵁ iX.opensRange ≤ iZ.opensRange)

/-- Restricting the actual ordinary invariant recovers the invariant of the ordinary restricted datum. -/
def invariantIso :
    (Scheme.Modules.restrictFunctor iY).obj
      (Geometric.CechInvariant.invariantSheaf f p q h (D.obj PUnit.unit) (OverlapPullback.overlapIso f D (q ≫ f) p q h rfl)) ≅
    Geometric.CechInvariant.invariantSheaf f' p' q' h' ((SquareGluing.pulledDatum f f' iX iY hf D).obj PUnit.unit)
      (OverlapPullback.overlapIso f' (SquareGluing.pulledDatum f f' iX iY hf D) (q' ≫ f') p' q' h' rfl) :=
  Open.CechInvariant.invariantIso f p q h f' p' q' h' iY iX iZ hf hp hq (D.obj PUnit.unit)
    (OverlapPullback.overlapIso f D (q ≫ f) p q h rfl) hfpre hqpre ≪≫
  Geometric.CechObjectChange.invariantIso f' p' q' h'
    ((Scheme.Modules.restrictFunctor iX).obj (D.obj PUnit.unit))
    ((SquareGluing.pulledDatum f f' iX iY hf D).obj PUnit.unit)
    (Open.CechInvariant.gluing p q p' q' iX iZ hp hq (D.obj PUnit.unit)
      (OverlapPullback.overlapIso f D (q ≫ f) p q h rfl))
    (OverlapPullback.overlapIso f' (SquareGluing.pulledDatum f f' iX iY hf D) (q' ≫ f') p' q' h' rfl)
    ((Scheme.Modules.restrictFunctorIsoPullback iX).app (D.obj PUnit.unit))
    (gluing_compatible f p q h f' p' q' h' iY iX iZ hf hp hq D)

include hp hq hfpre hqpre in
/-- Local ordinary effectivity is equivalent to invertibility of the restricted global comparison. -/
theorem comparison_map_isIso_iff :
    IsIso ((Scheme.Modules.restrictFunctor iX).map
      (Geometric.CechInvariant.comparison f p q h (D.obj PUnit.unit) (OverlapPullback.overlapIso f D (q ≫ f) p q h rfl))) ↔
    IsIso (Geometric.CechInvariant.comparison f' p' q' h' ((SquareGluing.pulledDatum f f' iX iY hf D).obj PUnit.unit)
      (OverlapPullback.overlapIso f' (SquareGluing.pulledDatum f f' iX iY hf D) (q' ≫ f') p' q' h' rfl)) :=
  (Open.CechInvariant.comparison_map_isIso_iff f p q h f' p' q' h' iY iX iZ hf hp hq
    (D.obj PUnit.unit) (OverlapPullback.overlapIso f D (q ≫ f) p q h rfl) hfpre hqpre).trans
  (Geometric.CechObjectChange.comparison_isIso_iff f' p' q' h'
    ((Scheme.Modules.restrictFunctor iX).obj (D.obj PUnit.unit))
    ((SquareGluing.pulledDatum f f' iX iY hf D).obj PUnit.unit)
    (Open.CechInvariant.gluing p q p' q' iX iZ hp hq (D.obj PUnit.unit)
      (OverlapPullback.overlapIso f D (q ≫ f) p q h rfl))
    (OverlapPullback.overlapIso f' (SquareGluing.pulledDatum f f' iX iY hf D) (q' ≫ f') p' q' h' rfl)
    ((Scheme.Modules.restrictFunctorIsoPullback iX).app (D.obj PUnit.unit))
    (gluing_compatible f p q h f' p' q' h' iY iX iZ hf hp hq D))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.OpenInvariant
