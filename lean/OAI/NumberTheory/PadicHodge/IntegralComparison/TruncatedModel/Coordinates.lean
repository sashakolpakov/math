import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicHomology

/-! # Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Coordinates.Comparison

noncomputable section

/-! The native additive comparison uses the same coefficient and
homology coordinates as the geometric common-cover comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem map_trans {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B C' : C} {D' : D}
    (e₁ : A ≅ B) (e₂ : B ≅ C') (e₃ : F.obj C' ≅ D') :
    F.mapIso (e₁ ≪≫ e₂) ≪≫ e₃ = F.mapIso e₁ ≪≫ (F.mapIso e₂ ≪≫ e₃) := by
  apply Iso.ext
  exact (congrArg (fun z => z ≫ e₃.hom) (F.map_comp e₁.hom e₂.hom)).trans
    (Category.assoc _ _ _)

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham.Comparison.coefficientFunctor p k
local notation "U" => ModuleCat.restrictScalars (algebraMap (WittVector p k) (OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n))
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n) X
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalDeRham.Comparison.rawComplex p k n X

omit [IsSeparated Y.hom] in
theorem iso_eq : GlobalDeRham.Comparison.iso p k n X Y f hp =
    MorphismIntrinsicCoordinates.Intrinsic.sourceIso p k n f hp :=
  map_trans ((G).mapHomologicalComplex (.up ℕ))
    (OrdinaryCechCoordinates.Ordinary.iso p k n X)
    (MorphismOrdinaryRefinement.Ordinary.sourceCoordinates p k n f hp)
    (MorphismCoefficientCech.sourceChosenIso p k n f hp)

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def homologyIso (i : ℕ) := MorphismIntrinsicHomology.Intrinsic.sourceIso p k n f hp i ≪≫
  GlobalFrame.Comparison.homologyIso p k n X Y f hp J i

theorem comparison_apply (i : ℕ) (x : (K).homology i) :
    IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X Y f hp J i x =
      (homologyIso p k n X Y f hp J i).hom
        (Witt.CoefficientCoordinates.addEquiv p k ((L).homology i)
          ((AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso U K i).inv x)) := by
  change (GlobalFrame.Comparison.homologyIso p k n X Y f hp J i).hom
      (HomologicalComplex.homologyMap
        (GlobalDeRham.Comparison.iso p k n X Y f hp).hom i
        ((AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso G L i).inv
          (Witt.CoefficientCoordinates.addEquiv p k ((L).homology i)
            ((AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso U K i).inv x)))) = _
  rw [iso_eq p k n X Y f hp]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Coordinates.Comparison
