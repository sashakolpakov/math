import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters

/-! # PEL Moduli -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli

noncomputable section

/-!
The fine moduli predicate is classification up to genuine isomorphism of
polarized, marked abelian schemes with integral action and prescribed Lie
ranks. The candidate record does not assert that such a moduli space exists.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}

/-- An isomorphism preserves every part of the PEL family, including the
Poincare bundle and the ordered full marking on all test schemes. -/
structure PELFamilyIso (A B : PEL.PELFamilyData R g N S) where
  abelian : A.abelian.scheme ≅ B.abelian.scheme
  dual : A.dual.abelian.scheme ≅ B.dual.abelian.scheme
  abelianGroup : IsMonHom abelian.hom
  dualGroup : IsMonHom dual.hom
  polarization : A.polarizationMap.hom ≫ dual.hom =
    abelian.hom ≫ B.polarizationMap.hom
  poincare : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (dual.hom ⊗ₘ abelian.hom).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare
  equivariant : ∀ r : R,
    End.endSchemeMap A.abelian.scheme (A.action r) ≫ abelian.hom =
      abelian.hom ≫ End.endSchemeMap B.abelian.scheme (B.action r)
  marking : ∀ (T : Over S)
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
    (A.marking.hom.app (.op T) c).val ≫ abelian.hom =
      (B.marking.hom.app (.op T) c).val

attribute [instance] PELFamilyIso.abelianGroup PELFamilyIso.dualGroup

namespace PELFamilyIso

variable {A B C : PEL.PELFamilyData R g N S}

def refl (A : PEL.PELFamilyData R g N S) : PELFamilyIso A A where
  abelian := Iso.refl _
  dual := Iso.refl _
  abelianGroup := inferInstanceAs (IsMonHom (𝟙 A.abelian.scheme))
  dualGroup := inferInstanceAs (IsMonHom (𝟙 A.dual.abelian.scheme))
  polarization := by simp
  poincare := by simp
  equivariant r := by simp
  marking T c := by simp

def productIso (e : PELFamilyIso A B) :
    (A.dual.abelian.scheme ⊗ A.abelian.scheme).left ≅
      (B.dual.abelian.scheme ⊗ B.abelian.scheme).left :=
  (Over.forget S).mapIso (e.dual ⊗ᵢ e.abelian)

def symm (e : PELFamilyIso A B) : PELFamilyIso B A where
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
    (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.productIso.inv) e.poincare.symm).trans
      ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackIso e.productIso).left_inv
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare))
  equivariant r := by
    apply (cancel_epi e.abelian.hom).mp
    simp only [Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← e.equivariant]
    simp
  marking T c := by
    calc
      _ = ((A.marking.hom.app (.op T) c).val ≫ e.abelian.hom) ≫
          e.abelian.inv := congrArg (fun a => a ≫ e.abelian.inv) (e.marking T c).symm
      _ = (A.marking.hom.app (.op T) c).val := by simp

def trans (e : PELFamilyIso A B) (f : PELFamilyIso B C) : PELFamilyIso A C where
  abelian := e.abelian ≪≫ f.abelian
  dual := e.dual ≪≫ f.dual
  abelianGroup := inferInstanceAs (IsMonHom (e.abelian.hom ≫ f.abelian.hom))
  dualGroup := inferInstanceAs (IsMonHom (e.dual.hom ≫ f.dual.hom))
  polarization := by
    simp only [Iso.trans_hom]
    rw [← Category.assoc, e.polarization, Category.assoc, f.polarization,
      ← Category.assoc]
  poincare := by
    have h : ((e.dual.hom ≫ f.dual.hom) ⊗ₘ (e.abelian.hom ≫ f.abelian.hom)).left =
        e.productIso.hom ≫ f.productIso.hom := by
      simp only [← tensorHom_comp_tensorHom, Over.comp_left]
      rfl
    exact (congrArg (fun a => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.dual.poincare)) h).trans
      ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp e.productIso.hom f.productIso.hom
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.dual.poincare)).trans
        ((congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.productIso.hom) f.poincare).trans
          e.poincare))
  equivariant r := by
    simp only [Iso.trans_hom]
    rw [← Category.assoc, e.equivariant, Category.assoc, f.equivariant,
      ← Category.assoc]
  marking T c := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ f.abelian.hom) (e.marking T c)).trans (f.marking T c))

end PELFamilyIso

/-- Isomorphism classes of genuine candidate PEL objects. -/
def pelFamilySetoid (R : Type u) [CommRing R] (g N : ℕ) (S : Scheme.{u}) :
    Setoid (PEL.PELFamilyData R g N S) where
  r A B := Nonempty (PELFamilyIso A B)
  iseqv := {
    refl A := ⟨PELFamilyIso.refl A⟩
    symm := fun ⟨e⟩ => ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

abbrev PELFamilyClass (R : Type u) [CommRing R] (g N : ℕ) (S : Scheme.{u}) :=
  Quotient (pelFamilySetoid R g N S)

variable {E : Type u} [Field E] [NumberField E] [NumberField.IsCMField E]
  {s : ℕ}

/-- The exact polarized-action-and-signature locus of the reference datum. -/
def IsPELFamily (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (baseAction : NumberField.RingOfIntegers E →+* Γ(S, ⊤))
    (D : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N S) : Prop :=
  D.IsPEL P.polarizationType
      (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom ∧
    D.HasPrescribedLieSignature P baseAction

/-- A candidate fine moduli space with a genuine family over it. No
classification, smoothness, properness, or existence is part of this data. -/
structure PELModuliCandidate (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (N : ℕ) (B : Scheme.{u}) where
  space : Over B
  family : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N space.left

namespace PELModuliCandidate

variable {B : Scheme.{u}} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  (M : PELModuliCandidate P N B)

/-- Classification on reduced test schemes, as in IntegralModel: pullbacks are PEL
families, and every PEL family has a unique classifying scheme morphism.
The isomorphism of families preserves polarization, action, and marking. -/
def ClassifiesReduced (baseAction : NumberField.RingOfIntegers E →+* Γ(B, ⊤)) : Prop :=
  (∀ (T : Over B) [IsReduced T.left] (x : T ⟶ M.space),
    IsPELFamily P (T.hom.appTop.hom.comp baseAction) (M.family.pullback x.left)) ∧
  ∀ (T : Over B) [IsReduced T.left]
    (D : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N T.left),
    IsPELFamily P (T.hom.appTop.hom.comp baseAction) D →
      ∃! x : T ⟶ M.space, Nonempty (PELFamilyIso (M.family.pullback x.left) D)

end PELModuliCandidate

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli
