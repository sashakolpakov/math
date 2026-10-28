import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionRowRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ZariskiSectionQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafCoproducts

/-! # Padic Diagonal Cech Comparison -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison

noncomputable section

/-! The actual native diagonal section complex maps globally to the
original crystalline injective resolution, compatibly with all open restrictions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp n
local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X Y f hp n
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

local instance sheafCoproducts : HasCoproducts.{0}
    (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :=
  Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts Rcoeff
    (IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n)

abbrev source := Section.DiagonalCone.SectionDiagonalCone.source X.left.affineOpens S P

def totalIso : CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp n ≅ CechCone.Total.CechConeTotal.total U P :=
  CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso
    (IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n)
    U (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.diagram p X Y f hp n)

def totalMap : source p X Y f hp n ⟶ ((S).mapHomologicalComplex (.up ℕ)).obj
    (CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp n) :=
  Section.DiagonalCech.SectionDiagonalCechComparison.map.{0, 2, 1, 1, 2} X.left.affineOpens Rcoeff S P H U ≫
    ((S).mapHomologicalComplex (.up ℕ)).map (totalIso p X Y f hp n).inv

variable (J : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

def map : source p X Y f hp n ⟶ ((S).mapHomologicalComplex (.up ℕ)).obj J.cocomplex :=
  totalMap p X Y f hp n ≫ ((S).mapHomologicalComplex (.up ℕ)).map
    (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n J)

variable (I : X.left.affineOpens) (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hi : I.val ≤ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i)

abbrev evaluate := (evaluation X.left.affineOpensᵒᵖ (ModuleCat.{2} Rcoeff)).obj (op I)
local notation "E" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.evaluate p X I

include hi in
theorem totalMap_evaluation_quasiIso : QuasiIso
    (((E).mapHomologicalComplex (.up ℕ)).map (totalMap p X Y f hp n)) := by
  have ha := Section.DiagonalCech.SectionDiagonalCechComparison.evaluation_quasiIso.{0, 2, 1, 1, 2}
    X.left.affineOpens Rcoeff S P H U I i hi
  let e := ((S).mapHomologicalComplex (.up ℕ)).mapIso (totalIso p X Y f hp n)
  let e' := ((E).mapHomologicalComplex (.up ℕ)).mapIso e
  have he : QuasiIso e'.inv := inferInstance
  rw [totalMap]
  erw [CategoryTheory.Functor.map_comp]
  exact (quasiIso_iff_comp_right _ e'.inv (hφ' := he)).mpr ha

include hi in
theorem evaluation_quasiIso : QuasiIso (((E).mapHomologicalComplex (.up ℕ)).map (IntrinsicPadicDiagonalCechComparison.map p X Y f hp n J)) := by
  let ha := totalMap_evaluation_quasiIso p X Y f hp n I i hi
  let hb : QuasiIso (((E).mapHomologicalComplex (.up ℕ)).map
      (((S).mapHomologicalComplex (.up ℕ)).map
        (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n J))) :=
    ZariskiSectionQuasiIso.IntrinsicPadicCechZariskiSectionQuasiIso.evaluation_quasiIso p X Y f hp n I J i hi
  rw [IntrinsicPadicDiagonalCechComparison.map]
  erw [CategoryTheory.Functor.map_comp]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison
