import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackCoordinates

/-! # Open Combined -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenCombined.FrameGeometricOpenCombined

noncomputable section

/-! The combined natural frame-resolution pullback respects the original
comparison to sections over inverse-image opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated fX] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)
  {FX : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n}
  {FY : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (a : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "Kn" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex fX n FX
local notation "Km" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex fY n FY
local notation "SX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) fX n
local notation "SY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) fY n
local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LargeOpenMap.BoundedGeometricLargeOpenMap.precompose (B := B) g

local instance constXZero :
    (Functor.const X.Opensᵒᵖ : ModuleCat.{u + 2} R ⥤ X.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl
local instance constYZero :
    (Functor.const Y.Opensᵒᵖ : ModuleCat.{u + 2} R ⥤ Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def map : ((SY).mapHomologicalComplex (.up ℕ)).obj Km ⟶
    ((SX ⋙ H).mapHomologicalComplex (.up ℕ)).obj Kn :=
  Section.CochainPullback.SectionCochainPullback.map T SY (SX ⋙ H) (Bounded.LargeOpenMap.BoundedGeometricLargeOpenMap.functorMap g hg n)
    (BoundedFrame.PullbackSheaf.BoundedFramePullbackSheaf.map g hg n FX FY a)

theorem map_eq : FrameGeometricOpenCombined.map g hg n a = OpenNaturality.FrameGeometricOpenNaturality.sectionsMap g hg n a :=
  congrArg (Section.CochainPullback.SectionCochainPullback.map T SY (SX ⋙ H) (Bounded.LargeOpenMap.BoundedGeometricLargeOpenMap.functorMap g hg n))
    (BoundedFrame.PullbackCoordinates.BoundedFramePullbackCoordinates.map_eq g hg n FX a)

theorem natural : (OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation fY n).app (op FY) ≫ FrameGeometricOpenCombined.map g hg n a =
    ((Functor.const Y.Opensᵒᵖ : ModuleCat.{u + 2} R ⥤ Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R).mapHomologicalComplex (.up ℕ)).map
      (((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
        (IntegralComparison.BoundedFrame.SectionChange.frameMap a)) ≫
          ((H).mapHomologicalComplex (.up ℕ)).map
            ((OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation fX n).app (op FX)) :=
  (congrArg (fun b => (OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation fY n).app (op FY) ≫ b)
    (map_eq g hg n a)).trans (OpenNaturality.FrameGeometricOpenNaturality.natural g hg n a)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenCombined.FrameGeometricOpenCombined
