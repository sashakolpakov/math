import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit
import Mathlib.CategoryTheory.Category.Preorder

/-! # Compact Support Inside Maps -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportInsideMaps

noncomputable section

/-!
# Ambient compact-support diagrams inside open subsets

These are restrictions of the existing relative-cohomology diagram to the
actual compact subsets contained in an open set. Inclusions of opens induce
canonical maps of the colimits, preserving every actual compact stage.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X : TopCat.{0}}

/-- Forget the containment condition on an actual compact support. -/
def compactsInsideForget (U : Opens X) : U.compactsInside ⥤ Compacts X :=
  (Subtype.mono_coe (· ∈ U.compactsInside)).functor

@[simp]
theorem compactsInsideForget_obj (U : Opens X) (K : U.compactsInside) :
    (compactsInsideForget U).obj K = K.val := rfl

/-- An inclusion of opens preserves the same actual compact support. -/
def compactsInsideMap {U V : Opens X} (h : U ≤ V) :
    U.compactsInside ⥤ V.compactsInside where
  obj K := ⟨K.val, fun _ hx => h (K.property hx)⟩
  map f := homOfLE (leOfHom f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
theorem compactsInsideMap_obj_val {U V : Opens X} (h : U ≤ V)
    (K : U.compactsInside) : ((compactsInsideMap h).obj K).val = K.val := rfl

@[simp]
theorem compactsInsideMap_forget {U V : Opens X} (h : U ≤ V) :
    compactsInsideMap h ⋙ compactsInsideForget V = compactsInsideForget U := rfl

@[simp]
theorem compactsInsideMap_id (U : Opens X) :
    compactsInsideMap (le_refl U) = 𝟭 U.compactsInside := rfl

@[simp]
theorem compactsInsideMap_comp {U V W : Opens X} (h : U ≤ V) (h' : V ≤ W) :
    compactsInsideMap h ⋙ compactsInsideMap h' = compactsInsideMap (h.trans h') := rfl

/-- The existing ambient relative-cohomology diagram restricted to compact supports in `U`. -/
def compactSupportInsideDiagram (M : ModuleCat.{0} R) (U : Opens X) (n : ℕ) :
    U.compactsInside ⥤ ModuleCat.{0} R :=
  compactsInsideForget U ⋙ CompactSupportCohomology.compactSupportCohomologyDiagram M X n

/-- The colimit over the genuine compact supports contained in `U`. -/
abbrev compactSupportedInsideCohomology (M : ModuleCat.{0} R) (U : Opens X) (n : ℕ) :
    ModuleCat.{0} R := colimit (compactSupportInsideDiagram M U n)

/-- Enlarge the allowed open set without changing any represented compact stage. -/
def compactSupportInsideMap (M : ModuleCat.{0} R) {U V : Opens X} (h : U ≤ V) (n : ℕ) :
    compactSupportedInsideCohomology M U n ⟶ compactSupportedInsideCohomology M V n :=
  colimit.pre (compactSupportInsideDiagram M V n) (compactsInsideMap h)

@[reassoc (attr := simp)]
theorem compactSupportInsideMap_ι (M : ModuleCat.{0} R) {U V : Opens X}
    (h : U ≤ V) (n : ℕ) (K : U.compactsInside) :
    colimit.ι (compactSupportInsideDiagram M U n) K ≫ compactSupportInsideMap M h n =
      colimit.ι (compactSupportInsideDiagram M V n) ((compactsInsideMap h).obj K) :=
  colimit.ι_pre (compactSupportInsideDiagram M V n) (compactsInsideMap h) K

@[simp]
theorem compactSupportInsideMap_id (M : ModuleCat.{0} R) (U : Opens X) (n : ℕ) :
    compactSupportInsideMap M (le_refl U) n = 𝟙 _ := by
  apply colimit.hom_ext
  intro K
  simp

@[reassoc (attr := simp)]
theorem compactSupportInsideMap_comp (M : ModuleCat.{0} R) {U V W : Opens X}
    (h : U ≤ V) (h' : V ≤ W) (n : ℕ) :
    compactSupportInsideMap M h n ≫ compactSupportInsideMap M h' n =
      compactSupportInsideMap M (h.trans h') n := by
  apply colimit.hom_ext
  intro K
  simp
  rfl

/-- Insertion of the restricted compact-support colimit into actual ambient `Hc`. -/
def compactSupportInsideToAmbient (M : ModuleCat.{0} R) (U : Opens X) (n : ℕ) :
    compactSupportedInsideCohomology M U n ⟶ CompactSupportCohomology.compactSupportedCohomology M X n :=
  colimit.pre (CompactSupportCohomology.compactSupportCohomologyDiagram M X n) (compactsInsideForget U) ≫
    (CompactSupportColimit.compactSupportCohomologyColimitIso M X n).hom

@[reassoc (attr := simp)]
theorem compactSupportInsideToAmbient_ι (M : ModuleCat.{0} R) (U : Opens X)
    (n : ℕ) (K : U.compactsInside) :
    colimit.ι (compactSupportInsideDiagram M U n) K ≫
        compactSupportInsideToAmbient M U n =
      CompactSupportCohomology.compactSupportCohomologyι M X K.val n := by
  simp [compactSupportInsideToAmbient, compactSupportInsideDiagram]

@[reassoc (attr := simp)]
theorem compactSupportInsideMap_toAmbient (M : ModuleCat.{0} R) {U V : Opens X}
    (h : U ≤ V) (n : ℕ) :
    compactSupportInsideMap M h n ≫ compactSupportInsideToAmbient M V n =
      compactSupportInsideToAmbient M U n := by
  apply colimit.hom_ext
  intro K
  simp

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportInsideMaps
