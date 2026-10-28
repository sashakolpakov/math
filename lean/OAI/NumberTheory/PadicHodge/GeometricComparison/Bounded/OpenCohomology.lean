import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LargeOpenMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.InjectivePullbackCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Open Cohomology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenCohomology.BoundedGeometricOpenCohomology

noncomputable section

/-! The actual geometric map on original injective open sections
induces exactly the original bounded crystalline Ext pullback globally. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)
  (IY : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) fY n))
  (IX : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) fX n))

local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport (p := p) (J := J) (δ := δ) g hg n
local notation "SX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) fX n
local notation "SY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) fY n
local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LargeOpenMap.BoundedGeometricLargeOpenMap.precompose (B := B) g
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LargeOpenMap.BoundedGeometricLargeOpenMap.functorMap (p := p) (J := J) (δ := δ) g hg n
local notation "VX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.evaluation (B := B) (⊤ : X.Opens)
local notation "VY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.evaluation (B := B) (⊤ : Y.Opens)

def openMap : IntegralComparison.BoundedOpen.SectionComplex.complex fY n IY ⟶
    ((H).mapHomologicalComplex (.up ℕ)).obj (IntegralComparison.BoundedOpen.SectionComplex.complex fX n IX) :=
  Section.CochainPullback.SectionCochainPullback.map T SY (SX ⋙ H) b (ExactInjective.ExactInjectivePullback.map T e IY IX)

def map : ((VY).mapHomologicalComplex (.up ℕ)).obj (IntegralComparison.BoundedOpen.SectionComplex.complex fY n IY) ⟶
    ((VX).mapHomologicalComplex (.up ℕ)).obj (IntegralComparison.BoundedOpen.SectionComplex.complex fX n IX) :=
  ((VY).mapHomologicalComplex (.up ℕ)).map (openMap g hg n IY IX)

def originalOpenMap : IntegralComparison.BoundedOpen.SectionComplex.complex fY n IY ⟶
    ((H).mapHomologicalComplex (.up ℕ)).obj (IntegralComparison.BoundedOpen.SectionComplex.complex fX n IX) :=
  Section.CochainPullback.SectionCochainPullback.map T SY (SX ⋙ H) b (IntegralComparison.BoundedGeneral.ResolutionMap.map g hg n IY IX)

def originalMap : ((VY).mapHomologicalComplex (.up ℕ)).obj (IntegralComparison.BoundedOpen.SectionComplex.complex fY n IY) ⟶
    ((VX).mapHomologicalComplex (.up ℕ)).obj (IntegralComparison.BoundedOpen.SectionComplex.complex fX n IX) :=
  ((VY).mapHomologicalComplex (.up ℕ)).map (originalOpenMap g hg n IY IX)

theorem map_eq : BoundedGeometricOpenCohomology.map g hg n IY IX = originalMap g hg n IY IX :=
  congrArg (fun a => ((VY).mapHomologicalComplex (.up ℕ)).map (Section.CochainPullback.SectionCochainPullback.map T SY (SX ⋙ H) b a))
    (InjectivePullbackCoordinates.BoundedInjectivePullbackCoordinates.map_eq g hg n IY IX)

theorem original_coordinates : (IntegralComparison.BoundedOpen.SectionGlobal.complexIso fY n IY).hom ≫ originalMap g hg n IY IX =
    IntegralComparison.BoundedGeneral.ResolutionPresheaf.map g hg n IY IX ≫ (IntegralComparison.BoundedOpen.SectionGlobal.complexIso fX n IX).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem coordinates : (IntegralComparison.BoundedOpen.SectionGlobal.complexIso fY n IY).hom ≫ BoundedGeometricOpenCohomology.map g hg n IY IX =
    IntegralComparison.BoundedGeneral.ResolutionPresheaf.map g hg n IY IX ≫ (IntegralComparison.BoundedOpen.SectionGlobal.complexIso fX n IX).hom :=
  (congrArg (fun a => (IntegralComparison.BoundedOpen.SectionGlobal.complexIso fY n IY).hom ≫ a) (map_eq g hg n IY IX)).trans
    (original_coordinates g hg n IY IX)

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (BoundedGeometricOpenCohomology.map g hg n IY IX) i ≫
    (IntegralComparison.BoundedOpen.SectionGlobal.homologyIso fX n IX i).hom =
      (IntegralComparison.BoundedOpen.SectionGlobal.homologyIso fY n IY i).hom ≫
        ModuleCat.ofHom (IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback g hg n i) := by
  have h₁ := IntegralComparison.InverseCoordinateHomology.homology
    (IntegralComparison.BoundedOpen.SectionGlobal.complexIso fY n IY) (IntegralComparison.BoundedOpen.SectionGlobal.complexIso fX n IX)
    (IntegralComparison.BoundedGeneral.ResolutionPresheaf.map g hg n IY IX) (BoundedGeometricOpenCohomology.map g hg n IY IX) (coordinates g hg n IY IX).symm i
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ (IntegralComparison.BoundedGeneral.ResolutionPresheaf.homology g hg n IY IX i)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenCohomology.BoundedGeometricOpenCohomology
