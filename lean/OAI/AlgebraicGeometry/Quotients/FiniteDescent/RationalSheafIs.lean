import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Rational Sheaf Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.RationalSheafIs.Construction.RationalSheaf

noncomputable section

/-! The module sheaf of rational functions on an integral scheme, including its empty-open value. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}} [IsIntegral X]

abbrev sections (U : X.Opens) := PLift (Nonempty U) → X.functionField

def scalarMap (U : X.Opens) : Γ(X, U) →+* sections U where
  toFun s h := let := h.down; X.germToFunctionField U s
  map_one' := by funext h; have := h.down; exact (X.germToFunctionField U).hom.map_one
  map_mul' s t := by funext h; have := h.down; exact (X.germToFunctionField U).hom.map_mul s t
  map_zero' := by funext h; have := h.down; exact (X.germToFunctionField U).hom.map_zero
  map_add' s t := by funext h; have := h.down; exact (X.germToFunctionField U).hom.map_add s t

instance (U : X.Opens) : Algebra Γ(X, U) (sections U) := (scalarMap U).toAlgebra

def restrict {U V : X.Opens} (h : V ≤ U) : sections U →+* sections V where
  toFun s hv := s ⟨⟨⟨hv.down.some.1, h hv.down.some.2⟩⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem scalar_restrict {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)) :
    restrict h (scalarMap U s) = scalarMap V (X.presheaf.map (homOfLE h).op s) := by
  funext hv
  have : Nonempty V := hv.down
  have : Nonempty U := ⟨⟨hv.down.some.1, h hv.down.some.2⟩⟩
  exact (X.presheaf.germ_res_apply (homOfLE h) (genericPoint X) _ s).symm

def restrictLinear {U V : X.Opens} (h : V ≤ U) :
    sections U →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] sections V where
  toFun s := restrict h s
  map_add' := (restrict h).map_add
  map_smul' r s := by
    change restrict h (scalarMap U r * s) =
      scalarMap V (X.presheaf.map (homOfLE h).op r) * restrict h s
    rw [map_mul, scalar_restrict]

def presheaf : PresheafOfModules X.ringCatSheaf.obj where
  obj U := ModuleCat.of Γ(X, U.unop) (sections U.unop)
  map {U V} h := ModuleCat.semilinearMapAddEquiv
    (show Γ(X, U.unop) →+* Γ(X, V.unop) from (X.presheaf.map h).hom)
    (ModuleCat.of Γ(X, U.unop) (sections U.unop))
    (ModuleCat.of Γ(X, V.unop) (sections V.unop)) (restrictLinear h.unop.le)
  map_id U := by ext s; rfl
  map_comp h g := by ext s; rfl

theorem intersection_nonempty (U V : X.Opens) (hU : Nonempty U) (hV : Nonempty V) :
    Nonempty (U ⊓ V : X.Opens) := by
  refine ⟨⟨genericPoint X, ?_, ?_⟩⟩
  · exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      ⟨hU.some.1, Set.mem_univ _, hU.some.2⟩
  · exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
      ⟨hV.some.1, Set.mem_univ _, hV.some.2⟩

theorem isSheaf : TopCat.Presheaf.IsSheaf (X := X) (RationalSheaf.presheaf (X := X)).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U s hs
  have he (i j : ι) (hi : Nonempty (U i)) (hj : Nonempty (U j)) : s i ⟨hi⟩ = s j ⟨hj⟩ :=
    congrFun (hs i j) ⟨intersection_nonempty (U i) (U j) hi hj⟩
  have hc (h : Nonempty (iSup U : X.Opens)) : ∃ i, Nonempty (U i) := by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp h.some.2
    exact ⟨i, ⟨⟨h.some.1, hi⟩⟩⟩
  let t : sections (iSup U) := fun h => s (hc h.down).choose ⟨(hc h.down).choose_spec⟩
  refine ⟨t, ?_, ?_⟩
  · intro i
    funext hi
    exact he _ i _ hi.down
  · intro z hz
    funext h
    exact congrFun (hz (hc h.down).choose) ⟨(hc h.down).choose_spec⟩

def sheaf : X.Modules where
  val := RationalSheaf.presheaf
  isSheaf := RationalSheaf.isSheaf

def inclusion : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ sheaf (X := X) where
  val.app U := ModuleCat.ofHom (R := Γ(X, U.unop))
    (X := Γ(X, U.unop)) (Y := sections U.unop)
    (Algebra.linearMap Γ(X, U.unop) (sections U.unop))
  val.naturality {U V} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change Γ(X, U.unop) at s
    funext hv
    exact congrFun (scalar_restrict h.unop.le s).symm hv

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.RationalSheafIs.Construction.RationalSheaf
