import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechCocycle
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleEffectiveDescent

/-! # Cocycle Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CocycleDescent

noncomputable section

/-!
# Effective descent of a genuine geometric affine line-bundle cocycle

The input is a geometric line bundle and an isomorphism of its two sheaf
pullbacks satisfying the geometric triple-overlap cocycle. The module
coaction and all its equations are constructed, rather than supplied.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechCocycle

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Ordinary geometric line-bundle gluing on the affine Čech overlap. -/
structure GeometricDatum where
  line : Line.Bundles.LineBundle (Spec (CommRingCat.of S))
  gluing : CechCocycle.pullbackAlong R S line.sheaf (Cech.ModuleModels.firstMap R S) ≅
    CechCocycle.pullbackAlong R S line.sheaf (Cech.ModuleModels.secondMap R S)
  cocycle : CechCocycle.IsCocycle R S line.sheaf gluing

end

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechCocycle

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The affine coordinate rings and scalar structures come from the given scheme morphism. -/
abbrev RingMapDatum := letI := f.hom.toAlgebra; GeometricDatum R S

/-- The module cocycle is obtained from the geometric cocycle by the canonical affine comparison. -/
def moduleLineDatum (D : RingMapDatum f) : CocycleEffectiveDescent.LineDatum f := by
  letI := f.hom.toAlgebra
  let M := (moduleSpecΓFunctor (R := S)).obj D.line.sheaf
  let e := QuasiCoherent.affineTildeIso D.line
  exact {
    line := D.line
    cech := {
      gluing := CechCocycle.moduleGluing R S D.line.sheaf D.gluing M e
      cocycle := CechCocycle.moduleGluing_cocycle R S D.line.sheaf D.gluing M e D.cocycle } }

/-- Faithfully flat descent constructs a genuine line bundle from the geometric Čech data. -/
def descendedLine [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat) (D : RingMapDatum f) :
    Line.Bundles.LineBundle (Spec R) :=
  CocycleEffectiveDescent.descendedLine f hf (moduleLineDatum f D)

/-- Pullback of the constructed line bundle recovers the original geometric line bundle. -/
def descendedLinePullbackIso [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat)
    (D : RingMapDatum f) :
    letI := f.hom.toAlgebra
    (Scheme.Modules.pullback (Spec.map f)).obj (descendedLine f hf D).sheaf ≅ D.line.sheaf := by
  letI := f.hom.toAlgebra
  exact CocycleEffectiveDescent.descendedLinePullbackIso f hf (moduleLineDatum f D)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CocycleDescent
