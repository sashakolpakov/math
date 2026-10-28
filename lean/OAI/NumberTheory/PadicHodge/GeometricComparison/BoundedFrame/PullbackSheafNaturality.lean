import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackPresheafNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackSheaf
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Pullback Sheaf Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackSheafNaturality.BoundedFramePullbackSheafNaturality

noncomputable section

/-! Arbitrary geometric pullback of original frame sheaf complexes is
natural under compatible changes of the source and target frames. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  {FX FX' : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {FY FY' : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (a : FX ⟶ FX') (b : FY ⟶ FY')
  (α : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)
  (α' : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX' ⟶ FY')

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "SX" => Functor.mapHomologicalComplex
  (IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n) (ComplexShape.up ℕ)

theorem natural (h : (G).map a ≫ α' = α ≫ b) :
    ((R).mapHomologicalComplex (.up ℕ)).map (IntegralComparison.BoundedFrame.Change.sheafMap b) ≫
      PullbackSheaf.BoundedFramePullbackSheaf.map g hg n FX FY α =
    PullbackSheaf.BoundedFramePullbackSheaf.map g hg n FX' FY' α' ≫ IntegralComparison.BoundedFrame.Change.sheafMap a := by
  have h₁ := (NatIso.mapHomologicalComplex
    (IntegralComparison.BoundedFrame.SheafRestriction.sheafificationIso g hg n) (.up ℕ)).hom.naturality
      (IntegralComparison.BoundedFrame.Change.presheafMap b)
  have h₂ := congrArg (SX).map
    (PullbackPresheafNaturality.BoundedFramePullbackPresheafNaturality.natural g hg n a b α α' h)
  simp only [Functor.map_comp] at h₂
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackSheafNaturality.BoundedFramePullbackSheafNaturality
