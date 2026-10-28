import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.ConstantRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.GeometricSectionMap

/-! # Pulled Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PulledSource

noncomputable section

/-! Pulling back the original constant frame source gives the actual coefficient-linear frame map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)
  {FX : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {FY : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (α : (BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

def sourceIso : ((R).mapHomologicalComplex (.up ℕ)).obj
    (((constantSheaf (BoundedCrystalline.Site.topology fY n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).obj
      (DeRhamSections.frameComplex fY n FY)) ≅
    ((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).obj
      (DeRhamSections.frameComplex fY n FY) :=
  (NatIso.mapHomologicalComplex (ConstantSection.ComplexRestriction.constantIso G (Crystalline.ExactRestriction.Coeff (B := B))
    (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n)) (.up ℕ)).app (DeRhamSections.frameComplex fY n FY)

omit [Fact p.Prime] [IsSeparated f] [IsSeparated fY] [Mono g] in
theorem component (i : ℕ) : (sourceIso g hg n (FY := FY)).inv.f i ≫
    (GeometricSectionMap.sourceMap g hg n α).f i =
      (constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).map
        ((SectionChange.frameMap α).f i) := by
  let e := ConstantSection.ComplexRestriction.constantIso G (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n)
  let b := (SectionChange.frameMap α).f i
  have hn := e.hom.naturality b
  have hx := ConstantRestriction.component g hg n FX i
  have h₁ := congrArg (fun a => (e.app _).inv ≫
    (R).map ((constantSheaf (BoundedCrystalline.Site.topology fY n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).map b) ≫ a) hx
  have h₂ := congrArg (fun a => (e.app _).inv ≫ a) hn
  exact h₁.trans (h₂.trans (Iso.inv_hom_id_assoc _ _))

omit [Fact p.Prime] [IsSeparated f] [IsSeparated fY] [Mono g] in
theorem complexes : (sourceIso g hg n (FY := FY)).inv ≫
    GeometricSectionMap.sourceMap g hg n α =
      ((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex (.up ℕ)).map
        (SectionChange.frameMap α) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact component g hg n α i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PulledSource
