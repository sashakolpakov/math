import OAI.AlgebraicGeometry.Crystalline.Cohomology.ConstantSheaf
import OAI.NumberTheory.PadicHodge.GeometricComparison.LinearAcyclicNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.LinearEquivTrans
import OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalDerived

/-! # Section Hypercohomology Inv -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SectionHypercohomologyInv.SectionHypercohomology

noncomputable section

/-! A linear and natural global-section calculation for bounded-below complexes with vanishing positive coefficient Ext. -/

open _root_.CategoryTheory Abelian Limits Opposite

theorem inverse_square {C : Type*} [Category* C] {A B A' B' : C}
    (e : A ≅ A') (d : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : f ≫ d.hom = e.hom ≫ g) : g ≫ d.inv = e.inv ≫ f := by
  rw [← cancel_epi e.hom, ← cancel_mono d.hom]
  simpa only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc, Category.comp_id] using h.symm

theorem map_inverse_square_apply {C : Type*} [Category* C] {R : Type*} [CommRing R]
    (F : C ⥤ ModuleCat R) {A B A' B' : C} (e : A ≅ A') (d : B ≅ B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : f ≫ d.hom = e.hom ≫ g) (a : F.obj A') :
    (F.mapIso d.symm).toLinearEquiv (F.map g a) =
      F.map f ((F.mapIso e.symm).toLinearEquiv a) :=
  congrArg (fun m : F.obj A' ⟶ F.obj B => m a)
    ((F.map_comp g d.inv).symm.trans ((congrArg F.map (inverse_square e d f g h)).trans
      (F.map_comp e.inv f)))

universe u

variable (R : Type u) [CommRing R] (X : TopCat.{u})

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ConstantSheaf.ConstantSheafSections.Sheaves R X
local notation "A" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ConstantSheaf.ConstantSheafSections.coefficient R X

local instance : EnoughInjectives V :=
  NumberTheory.PadicHodge.IntegralComparison.Module.SheafUniverses.enoughInjectives.{u, u, u} (Opens.grothendieckTopology X) R

local instance : HasExt.{u + 1} V := HasExt.standard _
local instance : HasDerivedCategory.{u + 1} V := HasDerivedCategory.standard _

abbrev sections : V ⥤ ModuleCat R :=
  (sheafSections (Opens.grothendieckTopology X) (ModuleCat R)).obj (op ⊤)

abbrev sectionComplex (K : CochainComplex V ℤ) : CochainComplex (ModuleCat R) ℤ :=
  ((sections R X).mapHomologicalComplex (.up ℤ)).obj K

def homSectionsIso (K : CochainComplex V ℤ) :
    Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K ≅ sectionComplex R X K :=
  ConstantSheaf.ConstantSheafSections.complexIso R X (.up ℤ) K

theorem homSectionsIso_naturality {K L : CochainComplex V ℤ} (f : K ⟶ L) :
    ((((linearCoyoneda R V).obj (op A)).mapHomologicalComplex (.up ℤ)).map f) ≫
      (homSectionsIso R X L).hom =
    (homSectionsIso R X K).hom ≫ ((sections R X).mapHomologicalComplex (.up ℤ)).map f := by
  ext n g
  exact ConstantSheaf.ConstantSheafSections.naturality R X g (f.f n)

theorem homSectionsIso_inv_naturality {K L : CochainComplex V ℤ} (f : K ⟶ L) :
    ((sections R X).mapHomologicalComplex (.up ℤ)).map f ≫ (homSectionsIso R X L).inv =
      (homSectionsIso R X K).inv ≫
        ((((linearCoyoneda R V).obj (op A)).mapHomologicalComplex (.up ℤ)).map f) := by
  exact inverse_square (homSectionsIso R X K) (homSectionsIso R X L) _ _
    (homSectionsIso_naturality R X f)

def homologyEquiv (K : CochainComplex V ℤ) (n : ℤ) :
    (sectionComplex R X K).homology n ≃ₗ[R] (Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K).homology n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) n).mapIso
    (homSectionsIso R X K).symm).toLinearEquiv

theorem homologyEquiv_naturality {K L : CochainComplex V ℤ} (f : K ⟶ L) (n : ℤ)
    (a : (sectionComplex R X K).homology n) :
    homologyEquiv R X L n (HomologicalComplex.homologyMap
      (((sections R X).mapHomologicalComplex (.up ℤ)).map f) n a) =
      HomologicalComplex.homologyMap
        ((((linearCoyoneda R V).obj (op A)).mapHomologicalComplex (.up ℤ)).map f) n
          (homologyEquiv R X K n a) :=
  map_inverse_square_apply (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) n)
    (homSectionsIso R X K) (homSectionsIso R X L) _ _ (homSectionsIso_naturality R X f) a

def comparisonSystem : NumberTheory.PadicHodge.GeometricComparison.NaturalDerived.NaturalDerivedComparison.System.{u + 1, u, u + 1, u + 1} (R := R) A :=
  NumberTheory.PadicHodge.GeometricComparison.NaturalDerived.NaturalDerivedComparison.constructed.{u + 1, u, u + 1, u + 1} (R := R) A

def derivedEquiv (K : CochainComplex V ℤ) (b : ℤ) [K.IsStrictlyGE b]
    (hK : ∀ p q, Subsingleton (Ext.{u + 1} A (K.X p) (q + 1))) (n : ℤ) :
    (Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K).homology n ≃ₗ[R]
      ((DerivedCategory.singleFunctor V 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :=
  (comparisonSystem R X).equiv K b hK n

theorem derivedEquiv_naturality {K L : CochainComplex V ℤ} (b c : ℤ)
    [K.IsStrictlyGE b] [L.IsStrictlyGE c]
    (hK : ∀ p q, Subsingleton (Ext.{u + 1} A (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext.{u + 1} A (L.X p) (q + 1)))
    (f : K ⟶ L) (n : ℤ) (a : (Comparison.Betti.LinearHomForget.Ext.integerLinearHomComplex (R := R) A K).homology n) :
    derivedEquiv R X L c hL n (HomologicalComplex.homologyMap
      ((((linearCoyoneda R V).obj (op A)).mapHomologicalComplex (.up ℤ)).map f) n a) =
      derivedEquiv R X K b hK n a ≫ (DerivedCategory.Q.map f)⟦n⟧' :=
  (comparisonSystem R X).naturality b c hK hL f n a

def equiv (K : CochainComplex V ℤ) (b : ℤ) [K.IsStrictlyGE b]
    (hK : ∀ p q, Subsingleton (Ext.{u + 1} A (K.X p) (q + 1))) (n : ℤ) :
    (sectionComplex R X K).homology n ≃ₗ[R]
      ((DerivedCategory.singleFunctor V 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :=
  (NumberTheory.PadicHodge.GeometricComparison.LinearEquivTrans.LinearEquivComposition.exists_trans (homologyEquiv R X K n)
    (derivedEquiv R X K b hK n)).choose

theorem equiv_apply (K : CochainComplex V ℤ) (b : ℤ) [K.IsStrictlyGE b]
    (hK : ∀ p q, Subsingleton (Ext.{u + 1} A (K.X p) (q + 1))) (n : ℤ)
    (a : (sectionComplex R X K).homology n) :
    SectionHypercohomology.equiv R X K b hK n a =
      derivedEquiv R X K b hK n
        (homologyEquiv R X K n a) :=
  (NumberTheory.PadicHodge.GeometricComparison.LinearEquivTrans.LinearEquivComposition.exists_trans (homologyEquiv R X K n)
    (derivedEquiv R X K b hK n)).choose_spec a

theorem naturality {K L : CochainComplex V ℤ} (b c : ℤ)
    [K.IsStrictlyGE b] [L.IsStrictlyGE c]
    (hK : ∀ p q, Subsingleton (Ext.{u + 1} A (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext.{u + 1} A (L.X p) (q + 1)))
    (f : K ⟶ L) (n : ℤ) (a : (sectionComplex R X K).homology n) :
    SectionHypercohomology.equiv R X L c hL n (HomologicalComplex.homologyMap
      (((sections R X).mapHomologicalComplex (.up ℤ)).map f) n a) =
      SectionHypercohomology.equiv R X K b hK n a ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  exact (equiv_apply R X L c hL n _).trans
    ((congrArg (derivedEquiv R X L c hL n)
      (homologyEquiv_naturality R X f n a)).trans
        ((derivedEquiv_naturality R X b c hK hL f n (homologyEquiv R X K n a)).trans
          (congrArg (fun z => z ≫ (DerivedCategory.Q.map f)⟦n⟧')
            (equiv_apply R X K b hK n a).symm)))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SectionHypercohomologyInv.SectionHypercohomology
