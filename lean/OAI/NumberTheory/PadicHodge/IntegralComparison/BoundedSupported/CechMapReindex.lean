import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechReindex

/-! # Cech Map Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechMapReindex

noncomputable section

/-! The actual coefficient-to-bounded-cohomology comparison is
natural under a finite-product-preserving change of principal indices. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem compose_square {A : Type*} [Category A]
    {K K' L L' Z : A} {s : K ⟶ K'} {t : L ⟶ L'}
    {a : K ⟶ L} {b : K' ⟶ L'} {c : L ⟶ Z} {d : L' ⟶ Z}
    (h₁ : a ≫ t = s ≫ b) (h₂ : t ≫ d = c) : s ≫ (b ≫ d) = a ≫ c := by
  rw [← Category.assoc, ← h₁, Category.assoc, h₂]

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteProducts r] (F : D ⥤ Y.Opens)
  {ι : Type u} [LinearOrder ι] (U : ι → C)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex.complex fY n I

local instance coefficient_limits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 2, u + 1}
local instance coefficient_colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasColimitsOfSize.{u + 2, u + 1, 0, 0} R

variable (L : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ)
  (a : L ⟶ Supported.OrderedCechEdge.presheafComplex.{u+1,u,u,u+2}
    (Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier F
    (BoundedOpen.FlasqueComplex.complex fY n I))

abbrev pulledSource := ((AugmentedOrdered.CechReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj L

def pulledMap : pulledSource r L ⟶
    Supported.OrderedCechEdge.presheafComplex.{u+1,u,u,u+2} R Y.carrier (r ⋙ F) K :=
  ((AugmentedOrdered.CechReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).map a

def sourceIso : (AugmentedOrdered.CechFunctor.bicomplex U (pulledSource r L)).total (.up ℕ) ≅
    (AugmentedOrdered.CechFunctor.bicomplex (r.obj ∘ U) L).total (.up ℕ) :=
  AugmentedOrdered.CechReindexTotal.totalIso r U L

theorem cochain :
    Cech.cochainMap fY n I (r ⋙ F) U (pulledSource r L) (pulledMap fY n I r F L a) ≫
      (CechReindex.totalIso fY n I r F U).hom =
    (sourceIso r U L).hom ≫ Cech.cochainMap fY n I F (r.obj ∘ U) L a :=
  AugmentedOrdered.CechReindexTotal.total_naturality r U L a

variable (O : Y.Opens) (hO : ∀ i, F.obj (r.obj (U i)) ≤ O)
  (hcoverC : (r ⋙ F).obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (r.obj (U i)))
  (hcoverD : F.obj (⊤_ D) ⊓ O ≤ ⨆ i, F.obj (r.obj (U i)))
  (hrowsC : ∀ q m, ((Cech.bicomplex fY n I (r ⋙ F) U).X q).ExactAt (m + 1))
  (hrowsD : ∀ q m, ((Cech.bicomplex fY n I F (r.obj ∘ U)).X q).ExactAt (m + 1))
  (hglobalC : (r ⋙ F).obj (⊤_ C) ⊔ O = ⊤)
  (hglobalD : F.obj (⊤_ D) ⊔ O = ⊤)

theorem comparison (i : ℕ) :
    HomologicalComplex.homologyMap (sourceIso r U L).hom i ≫
      Cech.map fY n I F (r.obj ∘ U) O hO hcoverD hrowsD hglobalD L a i =
    Cech.map fY n I (r ⋙ F) U O hO hcoverC hrowsC hglobalC
      (pulledSource r L) (pulledMap fY n I r F L a) i := by
  have hc := congrArg (fun m => HomologicalComplex.homologyMap m i) (cochain fY n I r F U L a)
  simp only [HomologicalComplex.homologyMap_comp] at hc
  exact compose_square hc
    (CechReindex.comparison fY n I r F U O hO hcoverC hcoverD
      hrowsC hrowsD hglobalC hglobalD i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechMapReindex
