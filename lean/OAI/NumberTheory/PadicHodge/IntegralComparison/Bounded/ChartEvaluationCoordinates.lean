import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartOpenImage

/-! # Chart Evaluation Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartEvaluationCoordinates

noncomputable section

/-! Coordinates of the original chart-to-open evaluation isomorphism, including its range transport. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B))
  (g : X ⟶ Y) [IsOpenImmersion g] (n : ℕ) (U : Y.Opens) (e : g.opensRange = U)

include e in
theorem property_iff (T : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n) :
    BoundedOpen.Subsite.property fY g n T ↔ BoundedOpen.SectionPresheaf.property fY n U T :=
  e ▸ ChartOpenImage.property_iff fY g n T

def linearEquiv (M : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n) :
    Incoming.SectionRestriction.Sections (Crystalline.ExactRestriction.Coeff (B := B)) (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B)))
      (BoundedOpen.Subsite.property fY g n) M.obj ≃ₗ[Crystalline.ExactRestriction.Coeff (B := B)]
    Incoming.SectionRestriction.Sections (Crystalline.ExactRestriction.Coeff (B := B)) (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B)))
      (BoundedOpen.SectionPresheaf.property fY n U) M.obj :=
  Incoming.EquivalentProperties.linearEquiv (Crystalline.ExactRestriction.Coeff (B := B))
    (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B)))
    (BoundedOpen.Subsite.property fY g n) (BoundedOpen.SectionPresheaf.property fY n U)
    (fun T hT => (property_iff fY g n U e T).mp hT)
    (fun T hT => (property_iff fY g n U e T).mpr hT) M.obj

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
  (p := p) (J := J) (δ := δ) fY n))

def iso : BoundedOpen.Resolution.complex fY g n I ≅
    ((BoundedOpen.SectionComplex.evaluation (B := B) U).mapHomologicalComplex (.up ℕ)).obj
      (BoundedOpen.SectionComplex.complex fY n I) :=
  ChartOpenImage.evaluationIso fY g n I ≪≫
    eqToIso (congrArg (fun V =>
      ((BoundedOpen.SectionComplex.evaluation (B := B) V).mapHomologicalComplex (.up ℕ)).obj
        (BoundedOpen.SectionComplex.complex fY n I)) e)

theorem component (i : ℕ) : (iso fY g n U e I).hom.f i =
    (ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).map
      (linearEquiv fY g n U e (I.cocomplex.X i)).toModuleIso.hom := by
  cases e
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartEvaluationCoordinates
