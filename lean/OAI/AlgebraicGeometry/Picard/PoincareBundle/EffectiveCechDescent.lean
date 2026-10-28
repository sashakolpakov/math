import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Cocycle
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Diagonal
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Symmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SwitchLineDescent

/-! # Effective Cech Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.EffectiveCechDescent

noncomputable section

/-!
# Effective descent from actual affine Čech gluing

The input consists of an isomorphism between the two actual scalar
extensions, with its diagonal, transposition, and triple-product
compatibilities. The coaction equations and effective descent are proved.
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct _root_.AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Switch OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Diagonal OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Symmetry OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Cocycle

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{u} S)

/-- Ordinary affine Čech gluing, expressed as actual module isomorphisms and diagrams. -/
structure CechDatum where
  gluing : Cech.ModuleModels.firstPullback R S M ≅ Cech.ModuleModels.secondPullback R S M
  diagonal : gluing.hom ≫ Cech.Diagonal.secondEvaluation R S M = Cech.Diagonal.firstEvaluation R S M
  symmetry : Cech.Symmetry.swappedHom R S M gluing = gluing.inv
  cocycle : Cech.TripleGluing.gluing12 R S M gluing ≫ Cech.TripleGluing.gluing23 R S M gluing = Cech.TripleGluing.gluing13 R S M gluing

/-- The coordinate switch determines the original gluing isomorphism. -/
theorem gluingSwitch_injective (σ τ : Cech.ModuleModels.firstPullback R S M ≅ Cech.ModuleModels.secondPullback R S M)
    (h : Cech.Switch.gluingSwitch R S M σ = Cech.Switch.gluingSwitch R S M τ) : σ = τ := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  apply (Cech.ModuleModels.secondModel R S M).injective
  have hh := DFunLike.congr_fun h (Cech.ModuleModels.firstModel R S M p)
  change Cech.ModuleModels.secondModel R S M (σ.hom ((Cech.ModuleModels.firstModel R S M).symm (Cech.ModuleModels.firstModel R S M p))) =
    Cech.ModuleModels.secondModel R S M (τ.hom ((Cech.ModuleModels.firstModel R S M).symm (Cech.ModuleModels.firstModel R S M p))) at hh
  erw [AddEquiv.symm_apply_apply] at hh
  exact hh

@[ext]
theorem CechDatum.ext (D E : CechDatum R S M) (h : D.gluing = E.gluing) : D = E := by
  cases D
  cases E
  cases h
  rfl

/-- The tensor descent switch extracted from the actual Čech diagrams. -/
def CechDatum.toSwitch (D : CechDatum R S M) :
    DescentSwitch.SwitchDatum R S ((restrictScalars (algebraMap R S)).obj M) where
  switch := Cech.Switch.gluingSwitch R S M D.gluing
  second_smul := Cech.Switch.gluingSwitch_second_smul R S M D.gluing
  diagonal_switch := Cech.Diagonal.gluingSwitch_diagonal R S M D.gluing D.diagonal
  involutive := Cech.Symmetry.gluingSwitch_involutive R S M D.gluing D.symmetry
  cocycle := Cech.Cocycle.gluingSwitch_cocycle R S M D.gluing D.cocycle

/-- Extracting the coaction loses no information from the original Čech gluing data. -/
theorem CechDatum.eq_of_coaction_eq (D E : CechDatum R S M)
    (h : D.toSwitch.coaction = E.toSwitch.coaction) : D = E := by
  apply CechDatum.ext
  exact gluingSwitch_injective R S M D.gluing E.gluing
    (DescentSwitch.SwitchDatum.switch_eq_of_coaction_eq D.toSwitch E.toSwitch h)

end

section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (M : ModuleCat.{u} S)

/-- The Čech diagrams with the algebra structure specified by the actual ring map. -/
abbrev RingMapDatum := letI := f.toAlgebra; CechDatum R S M

/-- The native Čech gluing gives the standard tensor switch with the ring-map scalar structures. -/
def ringMapSwitch (D : RingMapDatum f M) : SwitchCoalgebra.SwitchDatum f M := by
  letI := f.toAlgebra
  exact D.toSwitch

/-- The actual extension/restriction coalgebra derived from ordinary affine Čech data. -/
def moduleDatum (D : RingMapDatum f M) : Affine.Descent.ModuleDatum f :=
  SwitchCoalgebra.moduleDatum f M (ringMapSwitch f M D)

/-- The module on the base constructed by effective descent of the Čech gluing. -/
def descendedModule (hf : f.FaithfullyFlat) (D : RingMapDatum f M) : ModuleCat.{u} R :=
  Affine.Descent.descendedModule f hf (moduleDatum f M D)

/-- Its actual scalar extension recovers the original module. -/
def baseChangeIso (hf : f.FaithfullyFlat) (D : RingMapDatum f M) :
    (extendScalars f).obj (descendedModule f M hf D) ≅ M :=
  Affine.Descent.baseChangeIso f hf (moduleDatum f M D)

/-- Effective descent recovers the full coaction derived from the original Čech gluing. -/
def descentDataIso (hf : f.FaithfullyFlat) (D : RingMapDatum f M) :
    (Comonad.comparison (extendRestrictScalarsAdj f)).obj (descendedModule f M hf D) ≅
      moduleDatum f M D :=
  Affine.Descent.descentDataIso f hf (moduleDatum f M D)

end

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- Actual affine Čech gluing on the global sections of a geometric line bundle. -/
structure LineDatum where
  line : Line.Bundles.LineBundle (Spec S)
  cech : RingMapDatum f.hom ((moduleSpecΓFunctor (R := S)).obj line.sheaf)

/-- The geometric descent coaction is derived from the Čech isomorphism and its diagrams. -/
def LineDatum.coactionDatum (D : LineDatum f) : Geometric.AffineDescent.LineDatum f where
  line := D.line
  coaction := (moduleDatum f.hom _ D.cech).a
  counit := (moduleDatum f.hom _ D.cech).counit
  coassoc := (moduleDatum f.hom _ D.cech).coassoc

/-- Effective descent produces a genuine line bundle on a noetherian affine base. -/
def descendedLine [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat) (D : LineDatum f) :
    Line.Bundles.LineBundle (Spec R) :=
  Geometric.AffineDescent.descend f hf D.coactionDatum

/-- The geometric pullback of the constructed line bundle recovers the given bundle. -/
def descendedLinePullbackIso [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat) (D : LineDatum f) :
    (Scheme.Modules.pullback (Spec.map f)).obj (descendedLine f hf D).sheaf ≅ D.line.sheaf :=
  Geometric.AffineDescent.descendPullbackIso f hf D.coactionDatum

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.EffectiveCechDescent
