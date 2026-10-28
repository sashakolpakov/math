import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.SectionConeRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechIndexedGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.FlasqueCechGlobal

/-! # Cech Cone Global -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison

noncomputable section

/-! The indexed flasque Cech comparison specializes to the original
bounded crystalline injective resolution and its canonical global edge. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C : Type v} [Category.{w} C] [HasBinaryProducts C] (F : C ⥤ Y.Opens)
  {ι : Type} (U : ι → C)
  [∀ (q : ℕ) (t : Fin (q + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

local instance coefficientRing : Ring R := (inferInstance : CommRing R).toRing

local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex.complex fY n I

def sections := FlasqueCechIndexedGlobal.FlasqueCechIndexedGlobalComparison.sections.{u + 1, u, u + 2} R Y.carrier K F

def global := FlasqueCechGlobal.FlasqueCechGlobalComparison.globalComplex.{u + 1, u, u + 2} R Y.carrier K

def cone := FlasqueCechIndexedGlobal.FlasqueCechIndexedGlobalComparison.cone.{u + 1, u, u + 2} R Y.carrier K F

def bicomplex := CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex (A := ModuleCat.{u + 2} R) U
  (((IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) fY n ⋙
    NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{u + 2} R) F).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex)

def map := FlasqueCechIndexedGlobal.FlasqueCechIndexedGlobalComparison.map.{u + 1, u, u + 2} R Y.carrier K F U

def productIso := FlasqueCechIndexedGlobal.FlasqueCechIndexedGlobalComparison.productIso.{u + 1, u, u + 2} R Y.carrier K F U

theorem map_product : map fY n I F U ≫ (productIso fY n I F U).hom =
    FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.map fY n I (F.obj ∘ U) :=
  FlasqueCechIndexedGlobal.FlasqueCechIndexedGlobalComparison.map_product.{u + 1, u, u + 2} R Y.carrier K F U

variable (hU : iSup (F.obj ∘ U) = ⊤)

include hU in
theorem quasiIso : QuasiIso (map fY n I F U) :=
  FlasqueCechIndexedGlobal.FlasqueCechIndexedGlobalComparison.quasiIso.{u + 1, u, u + 2} R Y.carrier K F U hU
    (IntegralComparison.BoundedOpen.FlasqueComplex.term_flasque fY n I)

def homologyIso (i : ℕ) : ((bicomplex fY n I F U).total (.up ℕ)).homology i ≅
    ModuleCat.of R (IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) fY n i) :=
  FlasqueCechIndexedGlobal.FlasqueCechIndexedGlobalComparison.homologyIso.{u + 1, u, u + 2} R Y.carrier K F U hU
    (IntegralComparison.BoundedOpen.FlasqueComplex.term_flasque fY n I) i ≪≫ IntegralComparison.BoundedOpen.SectionGlobal.homologyIso fY n I i

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (map fY n I F U) i ≫
    (homologyIso fY n I F U hU i).hom = (IntegralComparison.BoundedOpen.SectionGlobal.homologyIso fY n I i).hom :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (IntegralComparison.BoundedOpen.SectionGlobal.homologyIso fY n I i).hom)
      (FlasqueCechIndexedGlobal.FlasqueCechIndexedGlobalComparison.homology.{u + 1, u, u + 2} R Y.carrier K F U hU
        (IntegralComparison.BoundedOpen.FlasqueComplex.term_flasque fY n I) i)).trans (Category.id_comp _))

universe s t

def refinedHomologyIso {D : Type s} [Category.{t} D]
    (G : C ⥤ D) (H : D ⥤ Y.Opens)
    [∀ (q : ℕ) (t : Fin (q + 1) → ι),
      PreservesLimit (Discrete.functor (U ∘ t)) (G ⋙ H)]
    (hCover : iSup ((G ⋙ H).obj ∘ U) = ⊤) (i : ℕ) :
    (((CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.target (A := ModuleCat.{u + 2} R) G U).obj
      (SectionConeRefinement.BoundedSectionConeRefinement.oldSections fY n I H)).total (.up ℕ)).homology i ≅
      ModuleCat.of R (IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology
        (p := p) (J := J) (δ := δ) fY n i) :=
  homologyIso fY n I (G ⋙ H) U hCover i

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison
