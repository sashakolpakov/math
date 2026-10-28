import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles

/-! # Scheme Ideal Module -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: actual algebraic line bundles on arbitrary schemes -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

/-- A genuine module sheaf locally isomorphic to the structure sheaf.
No cycle, Chern class, or compatibility assertion enters the data. -/
structure SchemeLineBundle (X : Scheme.{0}) where
  sheaf : X.Modules
  locallyTrivial : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (sheaf.restrict U.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme)

namespace SchemeLineBundle

variable {X : Scheme.{0}} (L : SchemeLineBundle X)

def trivializingOpen (x : X) : X.Opens := (L.locallyTrivial x).choose

theorem mem_trivializingOpen (x : X) : x ∈ L.trivializingOpen x := (L.locallyTrivial x).choose_spec.1

def trivialization (x : X) :
    L.sheaf.restrict (L.trivializingOpen x).ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule (L.trivializingOpen x).toScheme :=
  (L.locallyTrivial x).choose_spec.2.some

def trivializationOn (x : X) (W : X.Opens) (h : W ≤ L.trivializingOpen x) :
    L.sheaf.restrict W.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule W.toScheme :=
  DivisorClass.Chern.Line.Bundles.Construction.restrictTrivialization (L.trivialization x) h

def trivial (X : Scheme.{0}) : SchemeLineBundle X where
  sheaf := DivisorClass.Chern.Line.Bundles.Construction.structureModule X
  locallyTrivial x := ⟨⊤, by trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩

def ofPresentation {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle X) :
    SchemeLineBundle X.carrier := ⟨L.sheaf, L.locallyTrivial⟩

end SchemeLineBundle

end

/-! The actual ideal module of a scheme morphism is the kernel of the
structure-module map to the pushforward structure module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X Z : Scheme.{0}} (f : Z ⟶ X)

def schemeStructurePushforwardOne :
    ((Scheme.Modules.pushforward f).obj (DivisorClass.Chern.Line.Bundles.Construction.structureModule Z)).sections :=
  PresheafOfModules.sectionsMk (fun U => (1 : Γ(Z, f ⁻¹ᵁ U.unop))) (fun {_ _} i => by
    change (Z.presheaf.map ((TopologicalSpace.Opens.map f.base).map i.unop).op) 1 = 1
    exact map_one _)

def schemeStructurePushforwardMap : DivisorClass.Chern.Line.Bundles.Construction.structureModule X ⟶
    (Scheme.Modules.pushforward f).obj (DivisorClass.Chern.Line.Bundles.Construction.structureModule Z) :=
  (SheafOfModules.unitHomEquiv
    ((Scheme.Modules.pushforward f).obj (DivisorClass.Chern.Line.Bundles.Construction.structureModule Z))).symm (schemeStructurePushforwardOne f)

theorem schemeStructurePushforwardMap_one (U : X.Opens) :
    (schemeStructurePushforwardMap f).app U (1 : Γ(X, U)) = (1 : Γ(Z, f ⁻¹ᵁ U)) := by
  have h := (SheafOfModules.unitHomEquiv
    ((Scheme.Modules.pushforward f).obj (DivisorClass.Chern.Line.Bundles.Construction.structureModule Z))).apply_symm_apply
      (schemeStructurePushforwardOne f)
  exact congrArg (fun s => s.val (.op U)) h

theorem schemeStructurePushforwardMap_apply (U : X.Opens) (r : Γ(X, U)) :
    (schemeStructurePushforwardMap f).app U r = f.app U r := by
  have h := (schemeStructurePushforwardMap f).app_smul r (1 : Γ(X, U))
  change (schemeStructurePushforwardMap f).app U (r * (1 : Γ(X, U))) =
    r • (schemeStructurePushforwardMap f).app U (1 : Γ(X, U)) at h
  rw [mul_one, schemeStructurePushforwardMap_one] at h
  exact h.trans (mul_one (f.app U r))

def schemeIdealModule : X.Modules := kernel (schemeStructurePushforwardMap f)

def schemeIdealModuleInclusion : schemeIdealModule f ⟶ DivisorClass.Chern.Line.Bundles.Construction.structureModule X :=
  kernel.ι (schemeStructurePushforwardMap f)

theorem schemeIdealModuleInclusion_structureMap :
    schemeIdealModuleInclusion f ≫ schemeStructurePushforwardMap f = 0 := kernel.condition _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule.BundleCycles
