import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.PushforwardComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorComparisonNaturality

/-! # Pushforward Sheaf Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.PushforwardSheafNaturality

noncomputable section

/-! Direct-image comparison of ordered Cech complexes is natural in the module sheaf for any scheme morphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

private theorem moduleComparison_square_comp
    {R : Type u} [CommRing R] {A B C D E F : ModuleCat.{u} R}
    (a : A ⟶ D) (b : B ⟶ E) (c : C ⟶ F)
    (u : A ⟶ B) (v : B ⟶ C) (u' : D ⟶ E) (v' : E ⟶ F)
    (h₁ : a ≫ u' = u ≫ b) (h₂ : b ≫ v' = v ≫ c) :
    a ≫ (u' ≫ v') = (u ≫ v) ≫ c :=
  (Category.assoc a u' v').symm.trans
    ((congrArg (fun w : A ⟶ E => w ≫ v') h₁).trans
      ((Category.assoc u b v').trans
        ((congrArg (fun w : B ⟶ F => u ≫ w) h₂).trans (Category.assoc u v c).symm)))

private theorem moduleProduct_comparison_square
    {R : Type u} [CommRing R] {ι : Type u} (A B C D : ι → ModuleCat.{u} R)
    (si : ∀ i, A i ⟶ B i) (ti : ∀ i, C i ⟶ D i)
    (ui : ∀ i, A i ⟶ C i) (vi : ∀ i, B i ⟶ D i)
    (hi : ∀ i, si i ≫ vi i = ui i ≫ ti i) :
    CategoryTheory.Limits.Pi.map si ≫ CategoryTheory.Limits.Pi.map vi =
      CategoryTheory.Limits.Pi.map ui ≫ CategoryTheory.Limits.Pi.map ti := by
  rw [CategoryTheory.Limits.Pi.map_comp_map, CategoryTheory.Limits.Pi.map_comp_map]
  exact congrArg (fun w : ∀ i, A i ⟶ D i => CategoryTheory.Limits.Pi.map w) (funext hi)

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]
variable (f : X ⟶ Y) (c : R →+* Γ(Y, ⊤)) {M N : X.Modules} (e : M ⟶ N)

theorem coefficientModulePresheafPushforwardAppIso_sheaf_naturality (V : Y.Opens) :
    ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor (f.appTop.hom.comp c)).map e).app (op (f ⁻¹ᵁ V)) ≫
        (CoefficientCech.PushforwardFactors.coefficientModulePresheafPushforwardAppIso f c N V).hom =
      (CoefficientCech.PushforwardFactors.coefficientModulePresheafPushforwardAppIso f c M V).hom ≫
        ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map ((Scheme.Modules.pushforward f).map e)).app
          (op V) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem coefficientCechFactorPushforwardIso_sheaf_naturality
    {ι : Type u} (U : ι → Y.Opens) (n : ℕ) (i : Fin (n + 1) → ι) :
    ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor (f.appTop.hom.comp c)).map e).app
        (op (∏ᶜ fun k => f ⁻¹ᵁ U (i k))) ≫
      (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f c N U n i).hom =
    (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f c M U n i).hom ≫
      ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map ((Scheme.Modules.pushforward f).map e)).app
        (op (∏ᶜ fun k => U (i k))) := by
  let FM := Coefficient.ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp c) M
  let FN := Coefficient.ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp c) N
  let V : Y.Opens := ∏ᶜ fun k => U (i k)
  let W : X.Opens := ∏ᶜ fun k => f ⁻¹ᵁ U (i k)
  let j : op W ⟶ op (f ⁻¹ᵁ V) :=
    (eqToIso (CoefficientCech.PushforwardFactors.preimageCechIntersection f U n i)).op.hom
  let α : FM ⟶ FN := (Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor (f.appTop.hom.comp c)).map e
  let pM := (CoefficientCech.PushforwardFactors.coefficientModulePresheafPushforwardAppIso f c M V).hom
  let pN := (CoefficientCech.PushforwardFactors.coefficientModulePresheafPushforwardAppIso f c N V).hom
  let q := ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map
    ((Scheme.Modules.pushforward f).map e)).app (op V)
  have hn : α.app (op W) ≫ FN.map j = FM.map j ≫ α.app (op (f ⁻¹ᵁ V)) :=
    (α.naturality j).symm
  have hp : α.app (op (f ⁻¹ᵁ V)) ≫ pN = pM ≫ q :=
    coefficientModulePresheafPushforwardAppIso_sheaf_naturality f c e V
  change α.app (op W) ≫ (FN.map j ≫ pN) = (FM.map j ≫ pM) ≫ q
  exact moduleComparison_square_comp (α.app (op W)) (α.app (op (f ⁻¹ᵁ V))) q
    (FM.map j) pM (FN.map j) pN hn hp

def orderedCoefficientCechObjectPushforwardFunctorIso (P : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (n : ℕ) :
    (Ordered.CoefficientCechFunctor.orderedCoefficientCechObjectFunctor (f.appTop.hom.comp c) (fun i => f ⁻¹ᵁ U i) n).obj P ≅
      (Ordered.CoefficientCechFunctor.orderedCoefficientCechObjectFunctor c U n).obj ((Scheme.Modules.pushforward f).obj P) :=
  PushforwardObjects.orderedCoefficientCechObjectPushforwardIso f c P U n

variable {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens)

private theorem orderedCoefficientCechObjectPushforwardFunctorIso_hom_eq_piMap
    (P : X.Modules) (n : ℕ) :
    (orderedCoefficientCechObjectPushforwardFunctorIso f c P U n).hom =
      CategoryTheory.Limits.Pi.map (fun i : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
        (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f c P U n i.1).hom) := by
  apply Pi.hom_ext
  intro i
  exact (PushforwardObjects.orderedCoefficientCechObjectPushforwardIso_hom_π f c P U n i).trans
    (CategoryTheory.Limits.Pi.map_π
      (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n => (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f c P U n j.1).hom) i).symm

theorem orderedCoefficientCechObjectPushforwardIso_sheaf_naturality (n : ℕ) :
    (Ordered.CoefficientCechFunctor.orderedCoefficientCechObjectFunctor (f.appTop.hom.comp c)
        (fun i => f ⁻¹ᵁ U i) n).map e ≫
      (orderedCoefficientCechObjectPushforwardFunctorIso f c N U n).hom =
    (orderedCoefficientCechObjectPushforwardFunctorIso f c M U n).hom ≫
      (Ordered.CoefficientCechFunctor.orderedCoefficientCechObjectFunctor c U n).map ((Scheme.Modules.pushforward f).map e) := by
  let A (i : Ordered.SectionCechIndices.OrderedCechIndex ι n) :=
    Ordered.CoefficientCechTerms.coefficientCechFactor (f.appTop.hom.comp c) M (fun k => f ⁻¹ᵁ U k) n i.1
  let B (i : Ordered.SectionCechIndices.OrderedCechIndex ι n) :=
    Ordered.CoefficientCechTerms.coefficientCechFactor (f.appTop.hom.comp c) N (fun k => f ⁻¹ᵁ U k) n i.1
  let C (i : Ordered.SectionCechIndices.OrderedCechIndex ι n) :=
    Ordered.CoefficientCechTerms.coefficientCechFactor c ((Scheme.Modules.pushforward f).obj M) U n i.1
  let D (i : Ordered.SectionCechIndices.OrderedCechIndex ι n) :=
    Ordered.CoefficientCechTerms.coefficientCechFactor c ((Scheme.Modules.pushforward f).obj N) U n i.1
  let si (i : Ordered.SectionCechIndices.OrderedCechIndex ι n) : A i ⟶ B i :=
    ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor (f.appTop.hom.comp c)).map e).app
      (op (∏ᶜ fun k => f ⁻¹ᵁ U (i.1 k)))
  let ti (i : Ordered.SectionCechIndices.OrderedCechIndex ι n) : C i ⟶ D i :=
    ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map ((Scheme.Modules.pushforward f).map e)).app
      (op (∏ᶜ fun k => U (i.1 k)))
  let m (i : Ordered.SectionCechIndices.OrderedCechIndex ι n) : A i ⟶ C i :=
    (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f c M U n i.1).hom
  let v (i : Ordered.SectionCechIndices.OrderedCechIndex ι n) : B i ⟶ D i :=
    (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f c N U n i.1).hom
  rw [orderedCoefficientCechObjectPushforwardFunctorIso_hom_eq_piMap f c U N n,
    orderedCoefficientCechObjectPushforwardFunctorIso_hom_eq_piMap f c U M n]
  change CategoryTheory.Limits.Pi.map si ≫ CategoryTheory.Limits.Pi.map v =
    CategoryTheory.Limits.Pi.map m ≫ CategoryTheory.Limits.Pi.map ti
  exact moduleProduct_comparison_square A B C D si ti m v
    (fun i => coefficientCechFactorPushforwardIso_sheaf_naturality f c e U n i.1)

theorem orderedCoefficientCechComplexPushforwardIso_sheaf_naturality :
    (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor (f.appTop.hom.comp c)
        (fun i => f ⁻¹ᵁ U i)).map e ≫
      (PushforwardComplex.orderedCoefficientCechComplexPushforwardIso f c N U).hom =
    (PushforwardComplex.orderedCoefficientCechComplexPushforwardIso f c M U).hom ≫
      (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map ((Scheme.Modules.pushforward f).map e) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact orderedCoefficientCechObjectPushforwardIso_sheaf_naturality f c e U n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.PushforwardSheafNaturality
