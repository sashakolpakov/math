import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Bundles -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles

noncomputable section

/-!
# ChernClass: algebraic line bundles and their transition units

An algebraic line bundle is a sheaf of modules locally isomorphic to the
structure sheaf. Transition units below are extracted from actual isomorphisms
of these sheaves; no cohomology class or compatibility assertion is a field.
This module does not yet construct a Chern class.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- An algebraic line bundle is an O_X-module sheaf locally isomorphic to O_X. -/
structure AlgebraicLineBundle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) where
  sheaf : X.carrier.Modules
  locallyTrivial :
    ∀ x : X.carrier, ∃ U : X.carrier.Opens,
      x ∈ U ∧
      Nonempty
        (Scheme.Modules.restrict sheaf U.ι ≅
          (SheafOfModules.unit U.toScheme.ringCatSheaf : U.toScheme.Modules))

namespace Construction

variable {X : Scheme}

/-- The structure sheaf, considered as a sheaf of modules over itself. -/
abbrev structureModule (X : Scheme) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The section map of an endomorphism of O_X, with its ring-module types explicit. -/
def structureModuleHom
    (f : structureModule X ⟶ structureModule X) (U : X.Opens) :
    Γ(X, U) →ₗ[Γ(X, U)] Γ(X, U) where
  toFun r := f.app U r
  map_add' r s := (f.app U).hom.map_add r s
  map_smul' r s := f.app_smul r s

/-- An O_X-linear endomorphism of O_X is multiplication by its value on 1. -/
theorem structureModule_hom_apply
    (f : structureModule X ⟶ structureModule X) (U : X.Opens)
    (r : Γ(X, U)) :
    structureModuleHom f U r = r * structureModuleHom f U 1 := by
  simpa only [smul_eq_mul, mul_one] using (structureModuleHom f U).map_smul r 1

/-- An automorphism of O_X gives an invertible regular function on each open. -/
def structureModuleIsoUnit
    (e : structureModule X ≅ structureModule X) (U : X.Opens) : Γ(X, U)ˣ where
  val := structureModuleHom e.hom U 1
  inv := structureModuleHom e.inv U 1
  val_inv := by
    rw [← structureModule_hom_apply e.inv U]
    have h := congrArg
      (fun f : structureModule X ⟶ structureModule X =>
        structureModuleHom f U 1) e.hom_inv_id
    exact h
  inv_val := by
    rw [← structureModule_hom_apply e.hom U]
    have h := congrArg
      (fun f : structureModule X ⟶ structureModule X =>
        structureModuleHom f U 1) e.inv_hom_id
    exact h

@[simp]
theorem structureModuleIsoUnit_val
    (e : structureModule X ≅ structureModule X) (U : X.Opens) :
    (structureModuleIsoUnit e U : Γ(X, U)) = structureModuleHom e.hom U 1 := rfl

@[simp]
theorem structureModuleIsoUnit_refl (U : X.Opens) :
    structureModuleIsoUnit (Iso.refl (structureModule X)) U = 1 := by
  apply Units.ext
  rfl

/-- Composition of sheaf automorphisms gives multiplication of their units. -/
theorem structureModuleIsoUnit_trans
    (e f : structureModule X ≅ structureModule X) (U : X.Opens) :
    structureModuleIsoUnit (e ≪≫ f) U =
      structureModuleIsoUnit e U * structureModuleIsoUnit f U := by
  apply Units.ext
  change structureModuleHom f.hom U (structureModuleHom e.hom U 1) =
    structureModuleHom e.hom U 1 * structureModuleHom f.hom U 1
  exact structureModule_hom_apply f.hom U _

/-- The extracted units commute with restriction of regular functions. -/
theorem structureModuleIsoUnit_restrict
    (e : structureModule X ≅ structureModule X) {U V : X.Opens} (h : U ≤ V) :
    Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom
      (structureModuleIsoUnit e V) = structureModuleIsoUnit e U := by
  apply Units.ext
  have hn := ConcreteCategory.congr_hom
    (e.hom.mapPresheaf.naturality (homOfLE h).op) (1 : Γ(X, V))
  change structureModuleHom e.hom U (X.presheaf.map (homOfLE h).op 1) =
    X.presheaf.map (homOfLE h).op (structureModuleHom e.hom V 1) at hn
  rw [map_one] at hn
  exact hn.symm

/-- Restrict a local trivialization along an inclusion of open subschemes. -/
def restrictTrivialization {M : X.Modules} {U W : X.Opens}
    (e : M.restrict U.ι ≅ structureModule U.toScheme) (h : W ≤ U) :
    M.restrict W.ι ≅ structureModule W.toScheme :=
  (show M.restrict W.ι ≅ (M.restrict U.ι).restrict (X.homOfLE h) from
    by simpa only [Scheme.homOfLE_ι, Scheme.Modules.restrict, Functor.comp_obj] using
      (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M) ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso (X.homOfLE h)

/-- Change from one actual sheaf trivialization to another on a common open. -/
def transitionUnit {M : X.Modules} {W : X.Opens}
    (e f : M.restrict W.ι ≅ structureModule W.toScheme) :
    Γ(W.toScheme, ⊤)ˣ :=
  structureModuleIsoUnit (e.symm ≪≫ f) ⊤

@[simp]
theorem transitionUnit_self {M : X.Modules} {W : X.Opens}
    (e : M.restrict W.ι ≅ structureModule W.toScheme) :
    transitionUnit e e = 1 := by
  simp [transitionUnit]

/-- The transition cocycle identity follows from cancellation of actual frames. -/
theorem transitionUnit_cocycle {M : X.Modules} {W : X.Opens}
    (e f g : M.restrict W.ι ≅ structureModule W.toScheme) :
    transitionUnit e f * transitionUnit f g = transitionUnit e g := by
  unfold transitionUnit
  rw [← structureModuleIsoUnit_trans]
  congr 1
  simp

end Construction

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : AlgebraicLineBundle X)

/-- Choose a genuine trivializing neighborhood at each algebraic point. -/
def trivializingOpen (x : X.carrier) : X.carrier.Opens :=
  (L.locallyTrivial x).choose

theorem mem_trivializingOpen (x : X.carrier) : x ∈ L.trivializingOpen x :=
  (L.locallyTrivial x).choose_spec.1

/-- The corresponding actual isomorphism of O_X-module sheaves. -/
def trivialization (x : X.carrier) :
    L.sheaf.restrict (L.trivializingOpen x).ι ≅
      Construction.structureModule (L.trivializingOpen x).toScheme :=
  (L.locallyTrivial x).choose_spec.2.some

/-- Restrict the chosen trivialization to any smaller open subscheme. -/
def trivializationOn (x : X.carrier) (W : X.carrier.Opens)
    (h : W ≤ L.trivializingOpen x) :
    L.sheaf.restrict W.ι ≅ Construction.structureModule W.toScheme :=
  Construction.restrictTrivialization (L.trivialization x) h

/-- The actual transition unit on a common subopen of two chart domains. -/
def transitionOn (x y : X.carrier) (W : X.carrier.Opens)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y) :
    Γ(W.toScheme, ⊤)ˣ :=
  Construction.transitionUnit (L.trivializationOn x W hx) (L.trivializationOn y W hy)

theorem transitionOn_cocycle (x y z : X.carrier) (W : X.carrier.Opens)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y)
    (hz : W ≤ L.trivializingOpen z) :
    L.transitionOn x y W hx hy * L.transitionOn y z W hy hz =
      L.transitionOn x z W hx hz :=
  Construction.transitionUnit_cocycle _ _ _

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles
