import OAI.ArithmeticGeometry.Descent.CMVariety.ModuliObjects

/-! # Unpolarized Comparisons -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.UnpolarizedComparisons.Abelian

noncomputable section

/-!
Comparisons retaining the group, dual Poincare class, level, and designated
endomorphisms. Equality of their transported polarization maps upgrades
the comparison to a full enhanced isomorphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {g N r : ℕ} {δ : Fin g → ℕ} {S : Scheme}

structure UnpolarizedEnhancedIso (A B : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S) where
  abelian : A.polarized.abelian.scheme ≅ B.polarized.abelian.scheme
  dual : A.polarized.dual.abelian.scheme ≅ B.polarized.dual.abelian.scheme
  abelianGroup : IsMonHom abelian.hom
  dualGroup : IsMonHom dual.hom
  poincare : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (dual.hom ⊗ₘ abelian.hom).left
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.polarized.dual.poincare) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.polarized.dual.poincare
  level : ∀ (T : Over S)
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
    (A.polarized.level.hom.app (.op T) c).val ≫ abelian.hom =
      (B.polarized.level.hom.app (.op T) c).val
  equivariant : ∀ i, A.endomorphism i ≫ abelian.hom = abelian.hom ≫ B.endomorphism i

attribute [instance] UnpolarizedEnhancedIso.abelianGroup UnpolarizedEnhancedIso.dualGroup

namespace UnpolarizedEnhancedIso

variable {A B C : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S}

def ofEnhanced (e : ModuliObjects.Abelian.EnhancedAbelianIso A B) : UnpolarizedEnhancedIso A B where
  abelian := e.polarized.abelian
  dual := e.polarized.dual
  abelianGroup := e.polarized.abelianGroup
  dualGroup := e.polarized.dualGroup
  poincare := e.polarized.poincare
  level := e.polarized.level
  equivariant := e.equivariant

def productIso (e : UnpolarizedEnhancedIso A B) :
    (A.polarized.dual.abelian.scheme ⊗ A.polarized.abelian.scheme).left ≅
      (B.polarized.dual.abelian.scheme ⊗ B.polarized.abelian.scheme).left :=
  (Over.forget S).mapIso (e.dual ⊗ᵢ e.abelian)

def symm (e : UnpolarizedEnhancedIso A B) : UnpolarizedEnhancedIso B A where
  abelian := e.abelian.symm
  dual := e.dual.symm
  abelianGroup := inferInstanceAs (IsMonHom e.abelian.inv)
  dualGroup := inferInstanceAs (IsMonHom e.dual.inv)
  poincare :=
    (congrArg (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.productIso.inv) e.poincare.symm).trans
      ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackIso e.productIso).left_inv
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.polarized.dual.poincare))
  level T c := by
    calc
      (B.polarized.level.hom.app (.op T) c).val ≫ e.abelian.inv =
          ((A.polarized.level.hom.app (.op T) c).val ≫ e.abelian.hom) ≫ e.abelian.inv :=
        congrArg (fun a => a ≫ e.abelian.inv) (e.level T c).symm
      _ = (A.polarized.level.hom.app (.op T) c).val := by simp
  equivariant i := by
    change B.endomorphism i ≫ e.abelian.inv = e.abelian.inv ≫ A.endomorphism i
    apply (cancel_epi e.abelian.hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← e.equivariant]
    simp

def trans (e : UnpolarizedEnhancedIso A B) (f : UnpolarizedEnhancedIso B C) :
    UnpolarizedEnhancedIso A C where
  abelian := e.abelian ≪≫ f.abelian
  dual := e.dual ≪≫ f.dual
  abelianGroup := inferInstanceAs (IsMonHom (e.abelian.hom ≫ f.abelian.hom))
  dualGroup := inferInstanceAs (IsMonHom (e.dual.hom ≫ f.dual.hom))
  poincare := by
    have h : ((e.dual.hom ≫ f.dual.hom) ⊗ₘ (e.abelian.hom ≫ f.abelian.hom)).left =
        e.productIso.hom ≫ f.productIso.hom := by
      simp only [← tensorHom_comp_tensorHom, Over.comp_left]
      rfl
    exact (congrArg (fun a => AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.polarized.dual.poincare)) h).trans
      ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp e.productIso.hom f.productIso.hom
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.polarized.dual.poincare)).trans
        ((congrArg (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.productIso.hom) f.poincare).trans e.poincare))
  level T c :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ f.abelian.hom) (e.level T c)).trans (f.level T c))
  equivariant i := by
    change A.endomorphism i ≫ (e.abelian.hom ≫ f.abelian.hom) =
      (e.abelian.hom ≫ f.abelian.hom) ≫ C.endomorphism i
    rw [← Category.assoc, e.equivariant, Category.assoc, f.equivariant, ← Category.assoc]

def transportedPolarization (e : UnpolarizedEnhancedIso A B) :
    A.polarized.abelian.scheme ⟶ A.polarized.dual.abelian.scheme :=
  e.abelian.hom ≫ B.polarized.polarization.isogeny.hom ≫ e.dual.inv

instance transportedPolarization_group (e : UnpolarizedEnhancedIso A B) :
    IsMonHom e.transportedPolarization :=
  inferInstanceAs (IsMonHom (e.abelian.hom ≫ B.polarized.polarization.isogeny.hom ≫ e.dual.inv))

def withPolarization (e : UnpolarizedEnhancedIso A B)
    (h : A.polarized.polarization.isogeny.hom ≫ e.dual.hom =
      e.abelian.hom ≫ B.polarized.polarization.isogeny.hom) : ModuliObjects.Abelian.EnhancedAbelianIso A B where
  polarized := {
    abelian := e.abelian
    dual := e.dual
    abelianGroup := e.abelianGroup
    dualGroup := e.dualGroup
    polarization := h
    poincare := e.poincare
    level := e.level }
  equivariant := e.equivariant

def enhancedIsoOfTransportedEq (e : UnpolarizedEnhancedIso A B)
    (f : UnpolarizedEnhancedIso A C)
    (h : e.transportedPolarization = f.transportedPolarization) : ModuliObjects.Abelian.EnhancedAbelianIso B C :=
  (e.symm.trans f).withPolarization (by
    change B.polarized.polarization.isogeny.hom ≫ (e.dual.inv ≫ f.dual.hom) =
      (e.abelian.inv ≫ f.abelian.hom) ≫ C.polarized.polarization.isogeny.hom
    apply (cancel_epi e.abelian.hom).mp
    apply (cancel_mono f.dual.inv).mp
    simpa only [UnpolarizedEnhancedIso.transportedPolarization, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using h)

end UnpolarizedEnhancedIso

end

end OAI.ArithmeticGeometry.Descent.CMVariety.UnpolarizedComparisons.Abelian
