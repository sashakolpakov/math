import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleCoalgebra
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleNormalization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Cocycle
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.AffineDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.EffectiveCechDescent

/-! # Cocycle Effective Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleEffectiveDescent

noncomputable section

/-!
# Effective descent from an invertible affine Čech cocycle
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct _root_.AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Switch OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Cocycle

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (M : ModuleCat.{u} S)

/-- Ordinary invertible affine gluing with just the triple-overlap cocycle. -/
structure CechCocycle where
  gluing : Cech.ModuleModels.firstPullback R S M ≅ Cech.ModuleModels.secondPullback R S M
  cocycle : Cech.TripleGluing.gluing12 R S M gluing ≫ Cech.TripleGluing.gluing23 R S M gluing = Cech.TripleGluing.gluing13 R S M gluing

/-- The actual module cocycle gives the switch from which both coalgebra laws are derived. -/
def CechCocycle.toSwitch (D : CechCocycle R S M) :
    CocycleSwitchNext.CocycleSwitch R S ((restrictScalars (algebraMap R S)).obj M) where
  switch := Cech.Switch.gluingSwitch R S M D.gluing
  second_smul := Cech.Switch.gluingSwitch_second_smul R S M D.gluing
  cocycle := Cech.Cocycle.gluingSwitch_cocycle R S M D.gluing D.cocycle

@[ext]
theorem CechCocycle.ext (D E : CechCocycle R S M) (h : D.gluing = E.gluing) : D = E := by
  cases D
  cases E
  cases h
  rfl

/-- Coaction extraction retains the entire original affine gluing isomorphism. -/
theorem CechCocycle.eq_of_coaction_eq (D E : CechCocycle R S M)
    (h : D.toSwitch.coaction = E.toSwitch.coaction) : D = E := by
  apply CechCocycle.ext
  apply EffectiveCechDescent.gluingSwitch_injective R S M D.gluing E.gluing
  exact CocycleNormalization.switch_eq_of_coaction_eq D.toSwitch E.toSwitch h

end

section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (M : ModuleCat.{u} S)

abbrev RingMapDatum := letI := f.toAlgebra; CechCocycle R S M

def ringMapSwitch (D : RingMapDatum f M) : CocycleCoalgebra.CocycleSwitch f M := by
  letI := f.toAlgebra
  exact D.toSwitch

/-- The module descent coalgebra is constructed from the ordinary Čech cocycle. -/
def moduleDatum (D : RingMapDatum f M) : Affine.Descent.ModuleDatum f :=
  CocycleCoalgebra.moduleDatum f M (ringMapSwitch f M D)

def descendedModule (hf : f.FaithfullyFlat) (D : RingMapDatum f M) : ModuleCat.{u} R :=
  Affine.Descent.descendedModule f hf (moduleDatum f M D)

/-- Effective faithfully flat descent recovers the original module. -/
def baseChangeIso (hf : f.FaithfullyFlat) (D : RingMapDatum f M) :
    (extendScalars f).obj (descendedModule f M hf D) ≅ M :=
  Affine.Descent.baseChangeIso f hf (moduleDatum f M D)

/-- It also recovers the entire coaction extracted from the original gluing. -/
def descentDataIso (hf : f.FaithfullyFlat) (D : RingMapDatum f M) :
    (Comonad.comparison (extendRestrictScalarsAdj f)).obj (descendedModule f M hf D) ≅
      moduleDatum f M D :=
  Affine.Descent.descentDataIso f hf (moduleDatum f M D)

end

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- A genuine line bundle with an invertible module Čech cocycle on its global sections. -/
structure LineDatum where
  line : Line.Bundles.LineBundle (Spec S)
  cech : RingMapDatum f.hom ((moduleSpecΓFunctor (R := S)).obj line.sheaf)

def LineDatum.coactionDatum (D : LineDatum f) : Geometric.AffineDescent.LineDatum f where
  line := D.line
  coaction := (moduleDatum f.hom _ D.cech).a
  counit := (moduleDatum f.hom _ D.cech).counit
  coassoc := (moduleDatum f.hom _ D.cech).coassoc

/-- The cocycle descends the actual line bundle over a noetherian affine base. -/
def descendedLine [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat) (D : LineDatum f) :
    Line.Bundles.LineBundle (Spec R) :=
  Geometric.AffineDescent.descend f hf D.coactionDatum

/-- The pullback of the descended line bundle recovers the given geometric line bundle. -/
def descendedLinePullbackIso [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat) (D : LineDatum f) :
    (Scheme.Modules.pullback (Spec.map f)).obj (descendedLine f hf D).sheaf ≅ D.line.sheaf :=
  Geometric.AffineDescent.descendPullbackIso f hf D.coactionDatum

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleEffectiveDescent
