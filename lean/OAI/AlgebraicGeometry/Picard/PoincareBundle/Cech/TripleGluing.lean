import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleExtension
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionComposition

/-! # Triple Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing

noncomputable section

/-!
# The actual three affine gluing maps on a common triple coordinate ring
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Switch OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleExtension
open OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeFunctor

/-- A functor carries a conjugated map to the corresponding conjugated comparison. -/
theorem map_conjugation {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X₁ X₂ Y₁ Y₂ : C} {Z : D}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (a : Y₁ ⟶ Y₂)
    (b₁ : F.obj Y₁ ⟶ Z) (b₂ : F.obj Y₂ ⟶ Z) (t : Z ⟶ Z)
    (h : F.map a ≫ b₂ = b₁ ≫ t) :
    F.map (e₁.hom ≫ a ≫ e₂.inv) ≫ (F.map e₂.hom ≫ b₂) =
      (F.map e₁.hom ≫ b₁) ≫ t := by
  have hc : F.map e₂.inv ≫ F.map e₂.hom = 𝟙 _ := by
    rw [← F.map_comp, e₂.inv_hom_id, F.map_id]
  rw [F.map_comp e₁.hom (a ≫ e₂.inv), F.map_comp a e₂.inv]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map e₂.inv) (F.map e₂.hom), hc, Category.id_comp, h]

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

local notation "U" => S ⊗[R] S
local notation "V" => (S ⊗[R] S) ⊗[R] S

/-- The first two coordinates in the affine triple fiber product. -/
def pair12 : U →+* V := algebraMap U V

/-- The first and third coordinates in the affine triple fiber product. -/
def pair13 : U →+* V :=
  (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : S →ₐ[R] U)
    (AlgHom.id R S)).toRingHom

/-- The second and third coordinates in the affine triple fiber product. -/
def pair23 : U →+* V :=
  (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight : S →ₐ[R] U)
    (AlgHom.id R S)).toRingHom

def slot1 : S →+* V := (pair12 R S).comp (ModuleModels.firstMap R S)
def slot2 : S →+* V := (pair12 R S).comp (ModuleModels.secondMap R S)
def slot3 : S →+* V := Algebra.TensorProduct.includeRight.toRingHom

theorem pair13_first : (pair13 R S).comp (ModuleModels.firstMap R S) = slot1 R S := by
  ext s
  change (s ⊗ₜ[R] (1 : S)) ⊗ₜ[R] (1 : S) = _
  rfl

theorem pair13_second : (pair13 R S).comp (ModuleModels.secondMap R S) = slot3 R S := by
  ext s
  change ((1 : S) ⊗ₜ[R] (1 : S)) ⊗ₜ[R] s = _
  rfl

theorem pair23_first : (pair23 R S).comp (ModuleModels.firstMap R S) = slot2 R S := by
  ext s
  change ((1 : S) ⊗ₜ[R] s) ⊗ₜ[R] (1 : S) = _
  rfl

theorem pair23_second : (pair23 R S).comp (ModuleModels.secondMap R S) = slot3 R S := by
  ext s
  change ((1 : S) ⊗ₜ[R] (1 : S)) ⊗ₜ[R] s = _
  rfl

variable (M : ModuleCat.{u} S)

/-- A pullback of the original module to one of the three coordinate slots. -/
abbrev slotModule (i : S →+* V) := (extendScalars i).obj M

/-- Extend the actual gluing map along a pair of triple-product coordinates. -/
def extendedGluing (i : U →+* V) (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M) :
    slotModule R S M (i.comp (ModuleModels.firstMap R S)) ⟶
      slotModule R S M (i.comp (ModuleModels.secondMap R S)) :=
  (extendScalarsComp (ModuleModels.firstMap R S) i).hom.app M ≫
    (extendScalars i).map σ.hom ≫ (extendScalarsComp (ModuleModels.secondMap R S) i).inv.app M

/-- Gluing from the first coordinate to the second coordinate. -/
def gluing12 (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M) :
    slotModule R S M (slot1 R S) ⟶ slotModule R S M (slot2 R S) :=
  extendedGluing R S M (pair12 R S) σ

/-- Gluing from the first coordinate to the third coordinate. -/
def gluing13 (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M) :
    slotModule R S M (slot1 R S) ⟶ slotModule R S M (slot3 R S) :=
  eqToHom (congrArg (slotModule R S M) (pair13_first R S).symm) ≫
    extendedGluing R S M (pair13 R S) σ ≫
      eqToHom (congrArg (slotModule R S M) (pair13_second R S))

/-- Gluing from the second coordinate to the third coordinate. -/
def gluing23 (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M) :
    slotModule R S M (slot2 R S) ⟶ slotModule R S M (slot3 R S) :=
  eqToHom (congrArg (slotModule R S M) (pair23_first R S).symm) ≫
    extendedGluing R S M (pair23 R S) σ ≫
      eqToHom (congrArg (slotModule R S M) (pair23_second R S))

/-- The first-coordinate module in the canonical three-factor tensor model. -/
def firstFlatModel : (restrictScalars (slot3 R S)).obj (slotModule R S M (slot1 R S)) ≅
    TripleExtension.tripleModule R S M :=
  (restrictScalars (slot3 R S)).mapIso
      ((extendScalarsComp (ModuleModels.firstMap R S) (pair12 R S)).app M) ≪≫ TripleExtension.firstTripleModel R S M

/-- The second-coordinate module in the canonical three-factor tensor model. -/
def secondFlatModel : (restrictScalars (slot3 R S)).obj (slotModule R S M (slot2 R S)) ≅
    TripleExtension.tripleModule R S M :=
  (restrictScalars (slot3 R S)).mapIso
      ((extendScalarsComp (ModuleModels.secondMap R S) (pair12 R S)).app M) ≪≫ TripleExtension.secondTripleModel R S M

/-- The first-to-second gluing map on the common triple ring is the last-factor switch. -/
theorem gluing12_model (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M) :
    (restrictScalars (slot3 R S)).map (gluing12 R S M σ) ≫ (secondFlatModel R S M).hom =
      (firstFlatModel R S M).hom ≫ TripleExtension.tripleSwitch R S M σ := by
  exact map_conjugation (restrictScalars (slot3 R S))
    ((extendScalarsComp (ModuleModels.firstMap R S) (pair12 R S)).app M)
    ((extendScalarsComp (ModuleModels.secondMap R S) (pair12 R S)).app M)
    ((extendScalars (pair12 R S)).map σ.hom)
    (TripleExtension.firstTripleModel R S M).hom (TripleExtension.secondTripleModel R S M).hom (TripleExtension.tripleSwitch R S M σ)
    (TripleExtension.tripleModel_naturality R S M σ)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing
