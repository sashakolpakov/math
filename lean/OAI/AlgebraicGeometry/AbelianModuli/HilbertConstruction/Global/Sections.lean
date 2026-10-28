import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates

/-! # Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

noncomputable section

/-! Global sections as actual module-sheaf maps, and scalars as endomorphisms of the structure module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- A compatible family of sections is determined by its value on the whole scheme. -/
def moduleSectionsTopEquiv (L : X.Modules) : L.sections ≃ Γ(L, ⊤) where
  toFun s := s.val (.op ⊤)
  invFun z := PresheafOfModules.sectionsMk
    (fun U => L.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op z)
    (fun {U V} h => by
      exact (ConcreteCategory.congr_hom
        (L.presheaf.map_comp (homOfLE (show U.unop ≤ ⊤ from le_top)).op h) z).symm)
  left_inv s := by
    apply Subtype.ext
    funext U
    exact s.property (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  right_inv z := ConcreteCategory.congr_hom (L.presheaf.map_id (.op ⊤)) z

/-- Global sections of a module sheaf are morphisms from the structure module. -/
def moduleSectionHomEquiv (L : X.Modules) : (Line.Bundles.structureModule X ⟶ L) ≃ Γ(L, ⊤) :=
  L.unitHomEquiv.trans (moduleSectionsTopEquiv L)

@[simp]
theorem moduleSectionHomEquiv_apply (L : X.Modules) (s : Line.Bundles.structureModule X ⟶ L) :
    moduleSectionHomEquiv L s = s.app ⊤ (1 : Γ(X, ⊤)) := rfl

/-- The scalar of a structure-module endomorphism determines that endomorphism uniquely. -/
theorem structureModuleEndValue_injective (X : Scheme.{u}) :
    Function.Injective (Frame.Coordinates.structureModuleEndValue X) :=
  (moduleSectionHomEquiv (Line.Bundles.structureModule X)).injective

/-- Every global function is the scalar of a structure-module endomorphism. -/
theorem structureModuleEndValue_surjective (X : Scheme.{u}) :
    Function.Surjective (Frame.Coordinates.structureModuleEndValue X) :=
  (moduleSectionHomEquiv (Line.Bundles.structureModule X)).surjective

/-- The endomorphism ring of the structure module is the ring of global functions. -/
def structureModuleEndRingEquiv (X : Scheme.{u}) : End (Line.Bundles.structureModule X) ≃+* Γ(X, ⊤) :=
  RingEquiv.ofBijective (Frame.Coordinates.structureModuleEndValue X)
    ⟨structureModuleEndValue_injective X, structureModuleEndValue_surjective X⟩

/-- A structure-module endomorphism is invertible exactly when its global scalar is a unit. -/
theorem structureModuleEnd_isIso_iff (a : End (Line.Bundles.structureModule X)) :
    IsIso a ↔ IsUnit (Frame.Coordinates.structureModuleEndValue X a) := by
  rw [← isUnit_iff_isIso]
  constructor
  · exact fun h => h.map (Frame.Coordinates.structureModuleEndValue X)
  · intro h
    have hi := h.map (structureModuleEndRingEquiv X).symm.toRingHom
    exact (congrArg IsUnit ((structureModuleEndRingEquiv X).symm_apply_apply a)).mp hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
