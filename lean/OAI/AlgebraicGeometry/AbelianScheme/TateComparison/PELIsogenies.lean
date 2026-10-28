import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PEL

/-! # PEL Isogenies -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies

noncomputable section

/-!
Isogenies in the concrete marked PEL moduli problem. The multiplier is a
natural number; the type of a q-Hecke isogeny uses multiplier q^h. All fields
are equations on actual morphisms, Poincare bundles, and full level points.
The compatibility of composites is proved below from these equations.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}

/-- Composition of finite flat surjective group-scheme morphisms. -/
def composeIsogeny {A B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (e : A.Isogeny B) (f : B.Isogeny C) : A.Isogeny C where
  hom := e.hom ≫ f.hom
  preservesGroup := inferInstance
  finite := inferInstanceAs (IsFinite (e.hom.left ≫ f.hom.left))
  flat := inferInstanceAs (Flat (e.hom.left ≫ f.hom.left))
  surjective := inferInstanceAs (Surjective (e.hom.left ≫ f.hom.left))

/-- A candidate PEL isogeny with multiplier n. The dual map is identified
by its Poincare equation, and the marking is transported by the isogeny. -/
structure PELIsogeny (A B : PEL.PELFamilyData R g N S) (n : ℕ) where
  isogeny : A.abelian.Isogeny B.abelian
  dualHom : B.dual.abelian.scheme ⟶ A.dual.abelian.scheme
  dualGroup : IsMonHom dualHom
  poincare : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      (𝟙 B.dual.abelian.scheme ⊗ₘ isogeny.hom).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (dualHom ⊗ₘ 𝟙 A.abelian.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)
  equivariant : ∀ b : R,
    End.endSchemeMap A.abelian.scheme (A.action b) ≫ isogeny.hom =
      isogeny.hom ≫ End.endSchemeMap B.abelian.scheme (B.action b)
  polarization : isogeny.hom ≫ B.polarizationMap.hom ≫ dualHom =
    A.polarizationMap.hom ^ n
  marking : ∀ (T : Over S)
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
    (A.marking.hom.app (.op T) c).val ≫ isogeny.hom =
      (B.marking.hom.app (.op T) c).val

attribute [instance] PELIsogeny.dualGroup

namespace PELIsogeny

variable {A B C : PEL.PELFamilyData R g N S} {n m : ℕ}

/-- Poincare duality reverses composition, proved by functorial pullback. -/
theorem poincare_comp (e : PELIsogeny A B n) (f : PELIsogeny B C m) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        (𝟙 C.dual.abelian.scheme ⊗ₘ (e.isogeny.hom ≫ f.isogeny.hom)).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.dual.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        ((f.dualHom ≫ e.dualHom) ⊗ₘ 𝟙 A.abelian.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) := by
  let p := (𝟙 C.dual.abelian.scheme ⊗ₘ e.isogeny.hom).left
  let r := (f.dualHom ⊗ₘ 𝟙 A.abelian.scheme).left
  have hf := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass p) f.poincare
  have he := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass r) e.poincare
  have h₁ : (𝟙 C.dual.abelian.scheme ⊗ₘ
      (e.isogeny.hom ≫ f.isogeny.hom)).left =
      p ≫ (𝟙 C.dual.abelian.scheme ⊗ₘ f.isogeny.hom).left := by
    dsimp [p]
    rw [← Over.comp_left, tensorHom_comp_tensorHom, Category.id_comp]
  have h₂ : p ≫ (f.dualHom ⊗ₘ 𝟙 B.abelian.scheme).left =
      r ≫ (𝟙 B.dual.abelian.scheme ⊗ₘ e.isogeny.hom).left := by
    dsimp [p, r]
    simp only [← Over.comp_left, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
  have h₃ : r ≫ (e.dualHom ⊗ₘ 𝟙 A.abelian.scheme).left =
      ((f.dualHom ≫ e.dualHom) ⊗ₘ 𝟙 A.abelian.scheme).left := by
    dsimp [r]
    rw [← Over.comp_left, tensorHom_comp_tensorHom, Category.id_comp]
  rw [h₁, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hf,
    ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, h₂, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, he,
    ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, h₃]

/-- The polarization factor of a composite is the product of its factors. -/
theorem polarization_comp (e : PELIsogeny A B n) (f : PELIsogeny B C m) :
    (e.isogeny.hom ≫ f.isogeny.hom) ≫ C.polarizationMap.hom ≫
        (f.dualHom ≫ e.dualHom) = A.polarizationMap.hom ^ (n * m) := by
  calc
    _ = e.isogeny.hom ≫
        (f.isogeny.hom ≫ C.polarizationMap.hom ≫ f.dualHom) ≫ e.dualHom := by
      simp only [Category.assoc]
    _ = e.isogeny.hom ≫ (B.polarizationMap.hom ^ m) ≫ e.dualHom := by
      rw [f.polarization]
    _ = (e.isogeny.hom ≫ B.polarizationMap.hom ≫ e.dualHom) ^ m := by
      rw [MonObj.pow_comp, MonObj.comp_pow]
    _ = A.polarizationMap.hom ^ (n * m) := by
      rw [e.polarization, pow_mul]

/-- Composition retains both the full marking and the polarization data. -/
def comp (e : PELIsogeny A B n) (f : PELIsogeny B C m) :
    PELIsogeny A C (n * m) where
  isogeny := composeIsogeny e.isogeny f.isogeny
  dualHom := f.dualHom ≫ e.dualHom
  dualGroup := inferInstance
  poincare := e.poincare_comp f
  equivariant b := by
    change End.endSchemeMap _ (A.action b) ≫ (e.isogeny.hom ≫ f.isogeny.hom) = _
    rw [← Category.assoc, e.equivariant, Category.assoc, f.equivariant,
      ← Category.assoc]
    rfl
  polarization := e.polarization_comp f
  marking T c := by
    change _ ≫ (e.isogeny.hom ≫ f.isogeny.hom) = _
    rw [← Category.assoc, e.marking, f.marking]

/-- The identity PEL isogeny has multiplier one. -/
def identity (A : PEL.PELFamilyData R g N S) : PELIsogeny A A 1 where
  isogeny := AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny.identity A.abelian
  dualHom := 𝟙 A.dual.abelian.scheme
  dualGroup := inferInstance
  poincare := rfl
  equivariant b := by simp [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny.identity]
  polarization := by simp [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny.identity]
  marking T c := by simp [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny.identity]

end PELIsogeny

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies
