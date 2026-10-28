import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormBase
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.SectionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars

/-! # Ordinary Form Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormSections.BaseAffineOrdinaryFormSections

noncomputable section

/-! # Ordinary form sections on the original affine chart over any commutative base and their top-section comparison -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.SectionTowers.BaseAffineSectionTowers.affineScheme k A

def presheaf (n : ℕ) : (Spec (CommRingCat.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A :=
  (NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars.presheaves A (NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleScalars.base A)).obj
    (OrdinaryFormBase.OrdinaryFormModulePresheaf.presheaf k (AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X) n)

def algHom (U : (Spec (CommRingCat.of A)).Opens) : CommAlgCat.of k A ⟶
    (AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U) :=
  CommAlgCat.ofHom {
    toRingHom := AlgebraicForms.AlgebraicDeRham.sectionBaseMap A (NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleScalars.base A) U
    commutes' r := (DFunLike.congr_fun (SectionTowers.BaseAffineSectionTowers.sectionBaseMap k A U) r).symm }

theorem algHom_naturality {U V : (Spec (CommRingCat.of A)).Opens} (f : op U ⟶ op V) :
    algHom k A U ≫ (AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).map f = algHom k A V := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  exact AlgebraicForms.AlgebraicDeRham.sectionBaseMap_naturality A (NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleScalars.base A) f a

def map (U : (Spec (CommRingCat.of A)).Opens) (n : ℕ) :
    OrdinaryFormBase.OrdinaryFormModulePresheaf.formModule k (CommAlgCat.of k A) n ⟶ (presheaf k A n).obj (op U) :=
  OrdinaryFormBase.OrdinaryFormModulePresheaf.formMap k (algHom k A U) n

theorem naturality {U V : (Spec (CommRingCat.of A)).Opens} (f : op U ⟶ op V) (n : ℕ) :
    BaseAffineOrdinaryFormSections.map k A U n ≫ (presheaf k A n).map f = BaseAffineOrdinaryFormSections.map k A V n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (DeRhamGlobalId.DeRhamGlobal.formMap_comp (algHom k A U)
    ((AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).map f) n x).symm.trans
      (congrArg (fun g => DeRhamGlobalId.DeRhamGlobal.formMap g n x) (algHom_naturality k A f))

theorem top_bijective (n : ℕ) : Function.Bijective (BaseAffineOrdinaryFormSections.map k A ⊤ n) := by
  let e := CommAlgCat.isoMk (AlgEquiv.ofBijective (algHom k A ⊤).hom
    (NumberTheory.PadicHodge.IntegralComparison.Affine.CoordinateSections.global_bijective A))
  have he : e.hom = algHom k A ⊤ := rfl
  let : IsIso (algHom k A ⊤) := he ▸ e.isIso_hom
  exact ConcreteCategory.bijective_of_isIso ((DeRhamGlobalId.DeRhamGlobal.formsFunctor n).map (algHom k A ⊤))

def restrictionMap (a : A) (n : ℕ) : (presheaf k A n).obj (op ⊤) ⟶
    (presheaf k A n).obj (op (PrimeSpectrum.basicOpen a : (Spec (CommRingCat.of A)).Opens)) :=
  (presheaf k A n).map (homOfLE (show (PrimeSpectrum.basicOpen a : (Spec (CommRingCat.of A)).Opens) ≤ ⊤
    from le_top)).op

theorem principal_naturality (a : A) (n : ℕ) :
    BaseAffineOrdinaryFormSections.map k A ⊤ n ≫ restrictionMap k A a n = BaseAffineOrdinaryFormSections.map k A (PrimeSpectrum.basicOpen a) n :=
  naturality k A (homOfLE (show (PrimeSpectrum.basicOpen a : (Spec (CommRingCat.of A)).Opens) ≤ ⊤
    from le_top)).op n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormSections.BaseAffineOrdinaryFormSections
