import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ImageSectionsIso

/-! # Open Sections Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.OpenSectionsIso.BoundedFrameOpenSectionsIso

noncomputable section

/-! The original frame section map remains invertible when its image open
is specified by an equality of opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ fY = f) (n : ℕ)
  {FX : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {FY : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "KY" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex fY n FY

def restriction (U : Y.Opens) : Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections (p := p) (J := J) (δ := δ) fY n ⟶
    IntegralComparison.BoundedOpen.SectionComplex.functor fY n ⋙ IntegralComparison.BoundedOpen.SectionComplex.evaluation (B := B) U where
  app F := ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation fY n).app F).app (op U)
  naturality _ _ a := congrArg (fun η => η.app (op U))
    ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation fY n).naturality a)

def map (U : Y.Opens) := ImageSectionsIso.BoundedFrameImageSectionsIso.globalMap n (FY := FY) ≫
  (NatTrans.mapHomologicalComplex (restriction (p := p) (J := J) (δ := δ) (fY := fY) n U) (.up ℕ)).app KY

variable (e : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ≅ FY)
  (hlocal : IsIso (IntegralComparison.BoundedFrame.DeRhamSections.sectionsMap f n FX))

include hlocal e in
theorem isIso (U : Y.Opens) (hU : U = g.opensRange) : IsIso (map n (FY := FY) U) := by
  let : IsIso e.hom := e.isIso_hom
  subst U
  exact ImageSectionsIso.BoundedFrameImageSectionsIso.isIso g hg n e.hom hlocal

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.OpenSectionsIso.BoundedFrameOpenSectionsIso
