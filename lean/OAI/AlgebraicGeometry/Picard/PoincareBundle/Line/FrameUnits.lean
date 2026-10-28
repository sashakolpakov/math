import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

/-! # Frame Units -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

noncomputable section

/-!
# The unit-valued ratio of two frames of an actual line sheaf
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}}

/-- A morphism from the structure sheaf is multiplication by its section at one. -/
theorem unit_hom_app {M : X.Modules} (a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (U : X.Opens) (x : Γ(X, U)) :
    a.app U x = x • a.app U (1 : Γ(X, U)) := by
  have h := (AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp a U).map_smul x (1 : Γ(X, U))
  change a.app U (x * (1 : Γ(X, U))) = x • a.app U (1 : Γ(X, U)) at h
  simpa only [mul_one] using h

/-- A structure-sheaf morphism is determined by its values at one on every open. -/
theorem unit_hom_ext {M : X.Modules} {a b : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M}
    (h : ∀ U : X.Opens, a.app U (1 : Γ(X, U)) = b.app U (1 : Γ(X, U))) : a = b := by
  apply M.unitHomEquiv.injective
  apply Subtype.ext
  funext U
  exact h U.unop

/-- The global function by which a structure-sheaf endomorphism multiplies. -/
def scalar (a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) : Γ(X, ⊤) :=
  a.app ⊤ (1 : Γ(X, ⊤))

@[simp]
theorem scalar_id : scalar (𝟙 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) = 1 := rfl

/-- Composition of structure-sheaf endomorphisms multiplies their actual global functions. -/
theorem scalar_comp (a b : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    scalar (a ≫ b) = scalar a * scalar b := by
  exact unit_hom_app b ⊤ (scalar a)

/-- Restriction of the global scalar is the local scalar of the same sheaf endomorphism. -/
theorem scalar_restrict (a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (U : X.Opens) :
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (scalar a) =
      a.app U (1 : Γ(X, U)) := by
  have h := ConcreteCategory.congr_hom
    (a.mapPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
  change a.app U (X.presheaf.map _ (1 : Γ(X, ⊤))) = _ at h
  rw [map_one] at h
  exact h.symm

/-- Global functions detect equality of structure-sheaf endomorphisms. -/
theorem scalar_injective : Function.Injective (scalar (X := X)) := by
  intro a b h
  apply unit_hom_ext
  intro U
  rw [← scalar_restrict, ← scalar_restrict, h]

/-- An automorphism of the structure sheaf supplies an actual invertible global function. -/
def unitOfIso (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) : Γ(X, ⊤)ˣ where
  val := scalar e.hom
  inv := scalar e.inv
  val_inv := by rw [← scalar_comp, e.hom_inv_id, scalar_id]
  inv_val := by rw [← scalar_comp, e.inv_hom_id, scalar_id]

/-- The actual unit ratio of two trivializations of the same line sheaf. -/
def frameRatio {M : X.Modules} (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) : Γ(X, ⊤)ˣ :=
  unitOfIso (s ≪≫ t.symm)

/-- Vanishing of the unit-valued obstruction is precisely equality of the two frames. -/
theorem frameRatio_eq_one_iff {M : X.Modules} (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) :
    frameRatio s t = 1 ↔ s = t := by
  constructor
  · intro h
    have hs : scalar (s.hom ≫ t.inv) = scalar (𝟙 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) :=
      congrArg Units.val h
    have he := scalar_injective hs
    apply Iso.ext
    apply (cancel_mono t.inv).mp
    exact he.trans t.hom_inv_id.symm
  · rintro rfl
    apply Units.ext
    exact congrArg scalar s.hom_inv_id

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits
