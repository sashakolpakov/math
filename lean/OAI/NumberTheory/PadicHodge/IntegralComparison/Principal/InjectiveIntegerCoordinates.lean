import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.InjectiveRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.IntegerSheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientHomologyNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechLocalizedExtension

/-! # Injective Integer Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerCoordinates

noncomputable section

/-! Integer coefficients for the original shifted injective-resolution
Cech complex. Forgetting them retains the literal additive complex;
the affine comparison then returns to the original single module. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Injective.Comparison

private theorem combined_square {D : Type*} [Category D]
    {A B C E P Q : D} (e₁ : A ≅ B) (e₂ : C ≅ E) (f₁ : P ≅ B) (f₂ : Q ≅ E)
    (a : A ⟶ C) (b : B ⟶ E) (c : P ⟶ Q)
    (ha : a ≫ e₂.hom = e₁.hom ≫ b) (hb : f₁.hom ≫ b = c ≫ f₂.hom) :
    a ≫ (e₂ ≪≫ f₂.symm).hom = (e₁ ≪≫ f₁.symm).hom ≫ c := by
  apply (cancel_mono f₂.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hb]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using ha

variable {X : Scheme.{u}} {C : Type u} [Preorder C] [HasFiniteProducts C]
  (G : C ⥤ X.Opens) {ι : Type u} [LinearOrder ι] (W : ι → C)
  (N : X.Modules) (c : ℕ)

abbrev forget : ModuleCat.{u} ℤ ⥤ AddCommGrpCat.{u} := forget₂ _ _

def complex : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} ℤ)) ℕ :=
  ((Additive.IntegerSheaf.sheaves X).mapHomologicalComplex (.up ℕ)).obj
    (ShiftedOpenInjectiveResolution.complex (AffinePrincipal.Injective.Comparison.sheaf N) c)

def presheaf : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} ℤ) ℕ :=
  Supported.OrderedCechEdge.presheafComplex.{0,u,u,u} ℤ X G (complex N c)

def total : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  (Supported.OrderedCechEdge.bicomplex.{0,u,u,u} ℤ X G W (complex N c)).total (.up ℕ)

def coefficientIso (q : ℕ) : forget.obj ((InjectiveIntegerCoordinates.total G W N c).homology q) ≅
    (AffinePrincipal.Injective.Comparison.target G W N c).homology q :=
  AugmentedCech.CoefficientTotal.homologyIso W forget (presheaf G N c) q

def bridge [N.IsQuasicoherent] (hG : ∀ r, IsAffineOpen (G.obj r)) (q : ℕ) :
    forget.obj ((InjectiveIntegerCoordinates.total G W N c).homology q) ≅
      (AffinePrincipal.Injective.Comparison.source G W N c).homology q :=
  coefficientIso G W N c q ≪≫ (AffinePrincipal.Injective.Comparison.homologyIso G W N c hG q).symm

variable (G₂ : C ⥤ X.Opens) (α : G₂ ⟶ G)

def restriction : InjectiveIntegerCoordinates.total G W N c ⟶ InjectiveIntegerCoordinates.total G₂ W N c :=
  Supported.OrderedCechRestriction.totalMap.{0,u,u,u} ℤ X G G₂ α W (complex N c)

theorem coefficient_restriction (q : ℕ) :
    forget.map (homologyMap (restriction G W N c G₂ α) q) ≫ (coefficientIso G₂ W N c q).hom =
      (coefficientIso G W N c q).hom ≫
        homologyMap (AffinePrincipal.InjectiveRestriction.targetMap G G₂ α W N c) q := by
  exact AugmentedCech.CoefficientHomologyNaturality.Total.homologyIso_naturality W forget
    (Supported.OrderedCechRestriction.presheafMap.{0,u,u,u} ℤ X G G₂ α (complex N c)) q

theorem bridge_restriction [N.IsQuasicoherent]
    (hG : ∀ r, IsAffineOpen (G.obj r)) (hG₂ : ∀ r, IsAffineOpen (G₂.obj r)) (q : ℕ) :
    forget.map (homologyMap (restriction G W N c G₂ α) q) ≫ (bridge G₂ W N c hG₂ q).hom =
      (bridge G W N c hG q).hom ≫
        homologyMap (AffinePrincipal.InjectiveRestriction.sourceMap G G₂ α W N c) q :=
  combined_square (coefficientIso G W N c q) (coefficientIso G₂ W N c q)
    (AffinePrincipal.Injective.Comparison.homologyIso G W N c hG q) (AffinePrincipal.Injective.Comparison.homologyIso G₂ W N c hG₂ q) _ _ _
    (coefficient_restriction G W N c G₂ α q)
    (AffinePrincipal.InjectiveRestriction.homology_square G G₂ α W N c hG hG₂ q)

variable {P : X.Modules} (f : N ⟶ P)

def complexMap : complex N c ⟶ complex P c :=
  ((Additive.IntegerSheaf.sheaves X).mapHomologicalComplex (.up ℕ)).map
    (ShiftedOpenInjectiveResolution.map (AffinePrincipal.Injective.Comparison.sheaf N) c ((SheafOfModules.toSheaf X.ringCatSheaf).map f))

def totalMap : InjectiveIntegerCoordinates.total G W N c ⟶ InjectiveIntegerCoordinates.total G W P c :=
  Supported.OrderedCechCoefficientNaturality.totalMap.{0,u,u,u} ℤ X G W (complexMap N c f)

theorem coefficient_naturality (q : ℕ) :
    forget.map (homologyMap (totalMap G W N c f) q) ≫ (coefficientIso G W P c q).hom =
      (coefficientIso G W N c q).hom ≫
        homologyMap (AffinePrincipal.Injective.Comparison.targetMap G W N c f) q := by
  exact AugmentedCech.CoefficientHomologyNaturality.Total.homologyIso_naturality W forget
    (Supported.OrderedCechCoefficientNaturality.presheafMap.{0,u,u,u} ℤ X G (complexMap N c f)) q

theorem bridge_naturality [N.IsQuasicoherent] [P.IsQuasicoherent]
    (hG : ∀ r, IsAffineOpen (G.obj r)) (q : ℕ) :
    forget.map (homologyMap (totalMap G W N c f) q) ≫ (bridge G W P c hG q).hom =
      (bridge G W N c hG q).hom ≫
        homologyMap (AffinePrincipal.Injective.Comparison.sourceMap G W N c f) q :=
  combined_square (coefficientIso G W N c q) (coefficientIso G W P c q)
    (AffinePrincipal.Injective.Comparison.homologyIso G W N c hG q) (AffinePrincipal.Injective.Comparison.homologyIso G W P c hG q) _ _ _
    (coefficient_naturality G W N c f q)
    (AffinePrincipal.Injective.Comparison.homology_naturality G W N c f hG q)

def globalComplex :=
  ((Supported.SectionsExcision.sections (D := ModuleCat.{u} ℤ) (⊤ : X.Opens)).mapHomologicalComplex
    (.up ℕ)).obj (complex N c)

def additiveGlobalComplex :=
  ((Supported.SectionsExcision.sections (D := AddCommGrpCat.{u}) (⊤ : X.Opens)).mapHomologicalComplex
    (.up ℕ)).obj (ShiftedOpenInjectiveResolution.complex (AffinePrincipal.Injective.Comparison.sheaf N) c)

def globalIso (q : ℕ) : forget.obj ((globalComplex N c).homology q) ≅
    (additiveGlobalComplex N c).homology q :=
  (((globalComplex N c).sc q).mapHomologyIso forget).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerCoordinates
