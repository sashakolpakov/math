import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData

/-! # Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms

noncomputable section

/-!
Actual isomorphisms in the polarized full-level moduli problem. They preserve
the group schemes, polarization morphism, Poincare class, and ordered level.
The equivalence relation is proved from identity, inverse, and composition.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {g N : ℕ} {δ : Fin g → ℕ} {S : Scheme.{u}}

/-- An isomorphism of the polarized abelian data with ordered full level. -/
structure LevelPreservingIso
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) where
  abelian : A.abelian.scheme ≅ B.abelian.scheme
  dual : A.dual.abelian.scheme ≅ B.dual.abelian.scheme
  abelianGroup : IsMonHom abelian.hom
  dualGroup : IsMonHom dual.hom
  polarization : A.polarization.isogeny.hom ≫ dual.hom =
    abelian.hom ≫ B.polarization.isogeny.hom
  poincare : Line.Bundles.LineBundle.pullbackClass (dual.hom ⊗ₘ abelian.hom).left
    (Line.Bundles.LineBundle.classOf B.dual.poincare) = Line.Bundles.LineBundle.classOf A.dual.poincare
  level : ∀ (T : Over S)
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
    (A.level.hom.app (.op T) c).val ≫ abelian.hom =
      (B.level.hom.app (.op T) c).val

attribute [instance] LevelPreservingIso.abelianGroup LevelPreservingIso.dualGroup

namespace LevelPreservingIso

variable {A B C : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}

/-- The product isomorphism acting on the Poincare bundle. -/
def productIso (e : LevelPreservingIso A B) :
    (A.dual.abelian.scheme ⊗ A.abelian.scheme).left ≅
      (B.dual.abelian.scheme ⊗ B.abelian.scheme).left :=
  (Over.forget S).mapIso (e.dual ⊗ᵢ e.abelian)

/-- Identity isomorphism of polarized data. -/
def refl (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) : LevelPreservingIso A A where
  abelian := Iso.refl _
  dual := Iso.refl _
  abelianGroup := inferInstanceAs (IsMonHom (𝟙 A.abelian.scheme))
  dualGroup := inferInstanceAs (IsMonHom (𝟙 A.dual.abelian.scheme))
  polarization := by simp
  poincare := by simp
  level T c := by simp

/-- Inverse isomorphism of polarized data. -/
def symm (e : LevelPreservingIso A B) : LevelPreservingIso B A where
  abelian := e.abelian.symm
  dual := e.dual.symm
  abelianGroup := inferInstanceAs (IsMonHom e.abelian.inv)
  dualGroup := inferInstanceAs (IsMonHom e.dual.inv)
  polarization := by
    apply (cancel_epi e.abelian.hom).1
    simp only [Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← e.polarization]
    simp
  poincare :=
    (congrArg (Line.Bundles.LineBundle.pullbackClass e.productIso.inv) e.poincare.symm).trans
      ((Line.Bundles.LineBundle.pullbackIso e.productIso).left_inv (Line.Bundles.LineBundle.classOf B.dual.poincare))
  level T c := by
    calc
      (B.level.hom.app (.op T) c).val ≫ e.abelian.inv =
          ((A.level.hom.app (.op T) c).val ≫ e.abelian.hom) ≫ e.abelian.inv :=
        congrArg (fun a => a ≫ e.abelian.inv) (e.level T c).symm
      _ = (A.level.hom.app (.op T) c).val := by simp

/-- Composition of isomorphisms of polarized data. -/
def trans (e : LevelPreservingIso A B) (f : LevelPreservingIso B C) :
    LevelPreservingIso A C where
  abelian := e.abelian ≪≫ f.abelian
  dual := e.dual ≪≫ f.dual
  abelianGroup := inferInstanceAs (IsMonHom (e.abelian.hom ≫ f.abelian.hom))
  dualGroup := inferInstanceAs (IsMonHom (e.dual.hom ≫ f.dual.hom))
  polarization := by
    simp only [Iso.trans_hom]
    calc
      A.polarization.isogeny.hom ≫ (e.dual.hom ≫ f.dual.hom) =
          (A.polarization.isogeny.hom ≫ e.dual.hom) ≫ f.dual.hom :=
        (Category.assoc _ _ _).symm
      _ = (e.abelian.hom ≫ B.polarization.isogeny.hom) ≫ f.dual.hom :=
        congrArg (fun a => a ≫ f.dual.hom) e.polarization
      _ = (e.abelian.hom ≫ f.abelian.hom) ≫ C.polarization.isogeny.hom := by
        rw [Category.assoc, f.polarization, ← Category.assoc]
  poincare := by
    have h : ((e.dual.hom ≫ f.dual.hom) ⊗ₘ (e.abelian.hom ≫ f.abelian.hom)).left =
        e.productIso.hom ≫ f.productIso.hom := by
      simp only [← tensorHom_comp_tensorHom, Over.comp_left]
      rfl
    exact (congrArg (fun a => Line.Bundles.LineBundle.pullbackClass a
      (Line.Bundles.LineBundle.classOf C.dual.poincare)) h).trans
      ((Line.Bundles.LineBundle.pullbackClass_comp e.productIso.hom f.productIso.hom
        (Line.Bundles.LineBundle.classOf C.dual.poincare)).trans
        ((congrArg (Line.Bundles.LineBundle.pullbackClass e.productIso.hom) f.poincare).trans
          e.poincare))
  level T c := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ f.abelian.hom) (e.level T c)).trans (f.level T c))

end LevelPreservingIso

/-- The isomorphism relation used by the moduli problem. -/
def polarizedLevelSetoid (g : ℕ) (δ : Fin g → ℕ) (N : ℕ) (S : Scheme.{u}) :
    Setoid (PolarizationData.PolarizedAbelianWithFullLevel g δ N S) where
  r A B := Nonempty (LevelPreservingIso A B)
  iseqv := {
    refl A := ⟨LevelPreservingIso.refl A⟩
    symm := fun ⟨e⟩ => ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

/-- Isomorphism classes in the concrete polarized full-level moduli problem. -/
def PolarizedLevelClasses (g : ℕ) (δ : Fin g → ℕ) (N : ℕ) (S : Scheme.{u}) :=
  Quotient (polarizedLevelSetoid g δ N S)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms
