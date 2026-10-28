import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionRowRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ZariskiSectionQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafCoproducts

/-! # Diagonal Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.DiagonalCech.Comparison

noncomputable section

/-! The actual native diagonal section complex maps globally to the
original crystalline injective resolution, compatibly with all open restrictions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.sections p k n X Y f
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionRowRestriction.meet_isIso p k n X Y f hp
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance sheafCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts Rcoeff
    (BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n)

abbrev source := GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source X.left.affineOpens S P

def totalIso : CechSheafResolution.complex p k n X Y f hp ≅ GeometricComparison.CechCone.Total.CechConeTotal.total U P :=
  GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso
    (Bounded.RelativeSheafComplex.sheafification (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n)
    U (CechPresheaf.diagram p k n X Y f hp)

def totalMap : source p k n X Y f hp ⟶ ((S).mapHomologicalComplex (.up ℕ)).obj
    (CechSheafResolution.complex p k n X Y f hp) :=
  GeometricComparison.Section.DiagonalCech.SectionDiagonalCechComparison.map.{0, 2, 1, 1, 2} X.left.affineOpens Rcoeff S P H U ≫
    ((S).mapHomologicalComplex (.up ℕ)).map (totalIso p k n X Y f hp).inv

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def map : source p k n X Y f hp ⟶ ((S).mapHomologicalComplex (.up ℕ)).obj J.cocomplex :=
  totalMap p k n X Y f hp ≫ ((S).mapHomologicalComplex (.up ℕ)).map
    (CechInjective.Comparison.map p k n X Y f hp J)

variable (I : X.left.affineOpens) (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X)
  (hi : I.val ≤ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X i).val)

abbrev evaluate := (evaluation X.left.affineOpensᵒᵖ (ModuleCat.{2} Rcoeff)).obj (op I)
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.DiagonalCech.Comparison.evaluate p k n X I

include hi in
theorem totalMap_evaluation_quasiIso : QuasiIso
    (((E).mapHomologicalComplex (.up ℕ)).map (totalMap p k n X Y f hp)) := by
  have ha := GeometricComparison.Section.DiagonalCech.SectionDiagonalCechComparison.evaluation_quasiIso.{0, 2, 1, 1, 2}
    X.left.affineOpens Rcoeff S P H U I i hi
  let e := ((S).mapHomologicalComplex (.up ℕ)).mapIso (totalIso p k n X Y f hp)
  let e' := ((E).mapHomologicalComplex (.up ℕ)).mapIso e
  have he : QuasiIso e'.inv := inferInstance
  rw [totalMap]
  erw [CategoryTheory.Functor.map_comp]
  exact (quasiIso_iff_comp_right _ e'.inv (hφ' := he)).mpr ha

include hi in
theorem evaluation_quasiIso : QuasiIso (((E).mapHomologicalComplex (.up ℕ)).map (Comparison.map p k n X Y f hp J)) := by
  let ha := totalMap_evaluation_quasiIso p k n X Y f hp I i hi
  let hb : QuasiIso (((E).mapHomologicalComplex (.up ℕ)).map
      (((S).mapHomologicalComplex (.up ℕ)).map
        (CechInjective.Comparison.map p k n X Y f hp J))) :=
    ZariskiSectionQuasiIso.Cech.evaluation_quasiIso p k n X Y f hp I J i hi
  rw [Comparison.map]
  erw [CategoryTheory.Functor.map_comp]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.DiagonalCech.Comparison
