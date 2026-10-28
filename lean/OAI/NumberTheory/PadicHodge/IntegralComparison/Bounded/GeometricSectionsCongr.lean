import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionCongr
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricOpenSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartEvaluationCoordinates

/-! # Geometric Sections Congr -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricSectionsCongr

noncomputable section

/-! Equality of geometric chart maps respects original incoming and geometric section coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g g' : X ⟶ Y) [Mono g] [Mono g'] (hg : g ≫ fY = fX) (hg' : g' ≫ fY = fX)
  (e : g = g') (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))

def openIso : BoundedOpen.Resolution.complex fY g n I ≅
    BoundedOpen.Resolution.complex fY g' n I :=
  eqToIso (congrArg (fun t => BoundedOpen.Resolution.complex fY t n I) e)

def sectionsIso : GeometricResolution.complex g hg n I ≅
    GeometricResolution.complex g' hg' n I :=
  ((Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2}
    (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology fX n)).mapHomologicalComplex (.up ℕ)).mapIso
      (ResolutionCongr.iso g g' hg hg' e n I)

theorem complexes : (GeometricOpenSections.complexIso g hg n I).hom ≫
    (sectionsIso g g' hg hg' e n I).hom =
      (openIso g g' e n I).hom ≫ (GeometricOpenSections.complexIso g' hg' n I).hom := by
  cases e
  let S := (Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2}
    (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) fX n)).mapHomologicalComplex (.up ℕ)
  exact (congrArg (fun a => (GeometricOpenSections.complexIso g hg n I).hom ≫ a)
    (S.map_id (GeometricResolution.resolution g hg n I).cocomplex)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)

variable [IsOpenImmersion g] [IsOpenImmersion g'] (U : Y.Opens)
  (eU : g.opensRange = U) (eU' : g'.opensRange = U)

omit [Mono g] in
theorem evaluation : (openIso g g' e n I).hom ≫
    (ChartEvaluationCoordinates.iso fY g' n U eU' I).hom =
      (ChartEvaluationCoordinates.iso fY g n U eU I).hom := by
  cases e
  exact Category.id_comp _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricSectionsCongr
