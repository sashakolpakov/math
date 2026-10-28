import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionExt
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ExtTransportCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.SectionCohomologyCoordinates

/-! # Resolution Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionPresheaf

noncomputable section

/-! Actual geometric restriction of the original resolution's presheaf sections computes the original bounded Ext pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  (IY : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  (IX : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) f n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "JX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n
local notation "JY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) fY n
local notation "AX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) f n
local notation "AY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) fY n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionMap.map g hg n IY IX
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionExt.sectionMap g hg n IY IX

def map : Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R JY IY.cocomplex ⟶
    Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R JX IX.cocomplex :=
  Sheaf.ExtTransportCoordinates.presheafMap G R JX JY IY.cocomplex IX.cocomplex e

theorem complexes : s ≫ (Sheaf.PresheafSectionComplex.complexIso R JX IX.cocomplex).hom =
    (Sheaf.PresheafSectionComplex.complexIso R JY IY.cocomplex).hom ≫ map g hg n IY IX :=
  Sheaf.ExtTransportCoordinates.complexes G R JX JY IY.cocomplex IX.cocomplex e

theorem ext_homology (i : ℕ) : HomologicalComplex.homologyMap s i ≫
    (InjectiveSectionCohomology.homologyIso R AX IX i).hom =
      (InjectiveSectionCohomology.homologyIso R AY IY i).hom ≫
        ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback g hg n i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact ResolutionExt.naturality g hg n IY IX i

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (map g hg n IY IX) i ≫
    (Sheaf.PresheafSectionComplex.homologyIso R JX IX i).hom =
      (Sheaf.PresheafSectionComplex.homologyIso R JY IY i).hom ≫
        ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback g hg n i) :=
  Sheaf.SectionCohomologyCoordinates.homology.{u + 1, u, u + 2} R JX JY IX IY
    s (map g hg n IY IX) i (ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback g hg n i))
    (complexes g hg n IY IX) (ext_homology g hg n IY IX i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionPresheaf
