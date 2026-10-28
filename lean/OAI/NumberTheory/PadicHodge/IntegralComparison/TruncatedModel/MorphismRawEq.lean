import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismNewFrameHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RefinedCechMapCoordinates

/-! # Morphism Raw Eq -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRawEq.OldFrameCoordinates

noncomputable section

section

/-! The original small-cover map with its coefficient complexes fixed
before forming the Čech total. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {Y : Over (Spec (CommRingCat.of k))} [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev sourceCoefficients : CochainComplex (X.left.affineOpensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
    (FrameDiagonalMap.source p k n X Y f hp)

abbrev targetCoefficients : CochainComplex (X.left.affineOpensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  ((SectionBifunctor.sections p k n X Y f).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex

def coefficientMap : sourceCoefficients p k n f hp ⟶ targetCoefficients p k n f I :=
  FrameInjective.Comparison.map p k n X Y f hp I

def namedMap : FrameCech.Complexes.source p k n X Y f hp ⟶
    FrameCech.Complexes.target p k n X Y f I :=
  Witt.RefinedCechMapCoordinates.map p k
    (CechSliceResolution.opens p k n X)
    (K := sourceCoefficients p k n f hp) (L := targetCoefficients p k n f I)
    (coefficientMap p k n f hp I)

theorem map_eq : FrameCech.Comparison.map p k n X Y f hp I =
    namedMap p k n f hp I := rfl

end

section

/-! Homology of the named original small-cover Čech map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {Y : Over (Spec (CommRingCat.of k))} [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

abbrev named_homology (q : ℕ) := congrArg
  (fun (a : FrameCech.Complexes.source p k n X Y f hp ⟶
      FrameCech.Complexes.target p k n X Y f I) => homologyMap a q)
  (map_eq p k n f hp I)

end

section

/-! Homology of the named original small-cover Čech map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {Y : Over (Spec (CommRingCat.of k))} [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

theorem named_first (q : ℕ) :
    (GlobalFrame.Comparison.homologyIso p k n X Y f hp I q).hom =
      homologyMap (namedMap p k n f hp I) q ≫
        (GlobalEdge.InjectiveCech.homologyIso p k n X Y f I q).hom := by
  rfl

end

/-! The original small-cover frame comparison through its checked typed map.
The map unfolds to the literal refined Čech map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {Y : Over (Spec (CommRingCat.of k))} [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

omit [IsSeparated Y.hom] in
omit [Fintype k] in
theorem old_comparison (q : ℕ) :
    (GlobalEdge.InjectiveCech.homologyIso p k n X Y f I q).hom =
      MorphismGlobalTypedHomology.targetOldComparison p k n f I q := rfl

abbrev old_first (q : ℕ) := named_first p k n f hp I q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRawEq.OldFrameCoordinates
