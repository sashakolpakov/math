import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The presheaf of isomorphism classes of polarized abelian schemes with full level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {g N : ℕ} {δ : Fin g → ℕ} {S S' S'' : Scheme.{u}}

/-- The moduli class of an actual polarized abelian scheme with full level. -/
def PolarizationData.PolarizedAbelianWithFullLevel.classOf (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) :
    Moduli.Isomorphisms.PolarizedLevelClasses g δ N S := Quotient.mk _ A

/-- Equality of moduli classes means an actual level-preserving isomorphism exists. -/
theorem PolarizationData.PolarizedAbelianWithFullLevel.classOf_eq_iff
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) :
    A.classOf = B.classOf ↔ Nonempty (Moduli.Isomorphisms.LevelPreservingIso A B) :=
  Quotient.eq

@[simp]
theorem Moduli.Isomorphisms.PolarizedLevelClasses.pullback_classOf (f : S' ⟶ S)
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) :
    Moduli.Isomorphisms.PolarizedLevelClasses.pullback f A.classOf = (A.pullback f).classOf := rfl

@[simp]
theorem Moduli.Isomorphisms.PolarizedLevelClasses.pullback_id (q : Moduli.Isomorphisms.PolarizedLevelClasses g δ N S) :
    Moduli.Isomorphisms.PolarizedLevelClasses.pullback (𝟙 S) q = q := by
  induction q using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨Moduli.Isomorphisms.LevelPreservingIso.pullbackId A⟩

/-- The contravariant composition law holds on moduli classes. -/
theorem Moduli.Isomorphisms.PolarizedLevelClasses.pullback_comp (f : S' ⟶ S) (h : S'' ⟶ S')
    (q : Moduli.Isomorphisms.PolarizedLevelClasses g δ N S) :
    Moduli.Isomorphisms.PolarizedLevelClasses.pullback (h ≫ f) q = Moduli.Isomorphisms.PolarizedLevelClasses.pullback h (Moduli.Isomorphisms.PolarizedLevelClasses.pullback f q) := by
  induction q using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨(Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A f h).symm⟩

/-- The moduli presheaf with arbitrary ordered full level. -/
def Moduli.Functor.polarizedLevelModuli (g : ℕ) (δ : Fin g → ℕ) (N : ℕ) :
    Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj S := Moduli.Isomorphisms.PolarizedLevelClasses g δ N S.unop
  map f := TypeCat.ofHom (Moduli.Isomorphisms.PolarizedLevelClasses.pullback f.unop)
  map_id S := by
    ext q
    exact Moduli.Isomorphisms.PolarizedLevelClasses.pullback_id q
  map_comp f h := by
    ext q
    exact Moduli.Isomorphisms.PolarizedLevelClasses.pullback_comp f.unop h.unop q

/-- The moduli problem restricted to schemes over a fixed base. -/
def Moduli.Functor.polarizedLevelModuliOver (g : ℕ) (δ : Fin g → ℕ) (N : ℕ) (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  (Over.forget S).op ⋙ Moduli.Functor.polarizedLevelModuli g δ N

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
