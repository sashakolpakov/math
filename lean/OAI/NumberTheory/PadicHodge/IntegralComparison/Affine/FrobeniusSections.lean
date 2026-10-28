import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.Coordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars

/-! # Frobenius Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusSections

noncomputable section

/-!
# IntegralComparison: canonical Frobenius form sections on every open of the original affine chart
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k C : Type u) [Field k] [Fintype k] [CommRing C] [Algebra k C]

abbrev scheme := Crystalline.Presentation.affineScheme k C

def presheaf (n : ℕ) : (Spec (CommRingCat.of C)).Opensᵒᵖ ⥤ ModuleCat.{u} C :=
  (AlgebraSheafScalars.presheaves C (ModuleScalars.base C)).obj
    ((Frobenius.DeRhamGlobal.presheafComplex k (scheme k C)).X n)

def algHom (U : (Spec (CommRingCat.of C)).Opens) : CommAlgCat.of k C ⟶
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k (scheme k C)).obj (op U) :=
  CommAlgCat.ofHom
    { toRingHom := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap C (ModuleScalars.base C) U
      commutes' r := (DFunLike.congr_fun (AffineSection.Towers.sectionBaseMap k C U) r).symm }

omit [Fintype k] in
theorem algHom_naturality {U V : (Spec (CommRingCat.of C)).Opens} (f : op U ⟶ op V) :
    algHom k C U ≫ (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k (scheme k C)).map f = algHom k C V := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro c
  exact AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap_naturality C (ModuleScalars.base C) f c

def map (U : (Spec (CommRingCat.of C)).Opens) (n : ℕ) :
    Frobenius.DeRhamComplex.forms k C n ⟶ (presheaf k C n).obj (op U) :=
  Frobenius.FormMaps.map (algHom k C U) n

theorem naturality {U V : (Spec (CommRingCat.of C)).Opens} (f : op U ⟶ op V) (n : ℕ) :
    FrobeniusSections.map k C U n ≫ (presheaf k C n).map f = FrobeniusSections.map k C V n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_comp (algHom k C U)
    ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k (scheme k C)).map f) n ω).symm.trans
      (congrArg (fun g => AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap g n ω) (algHom_naturality k C f))

omit [Fintype k] in
theorem algHom_top_bijective : Function.Bijective (algHom k C ⊤).hom :=
  CoordinateSections.global_bijective C

theorem top_bijective (n : ℕ) : Function.Bijective (FrobeniusSections.map k C ⊤ n) := by
  let e := CommAlgCat.isoMk (AlgEquiv.ofBijective (algHom k C ⊤).hom (algHom_top_bijective k C))
  have he : e.hom = algHom k C ⊤ := rfl
  let : IsIso (algHom k C ⊤) := he ▸ e.isIso_hom
  exact ConcreteCategory.bijective_of_isIso ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsFunctor n).map (algHom k C ⊤))

def restrictionMap (c : C) (n : ℕ) : (presheaf k C n).obj (op ⊤) ⟶
    (presheaf k C n).obj (op (PrimeSpectrum.basicOpen c : (Spec (CommRingCat.of C)).Opens)) :=
  (presheaf k C n).map (homOfLE (show (PrimeSpectrum.basicOpen c : (Spec (CommRingCat.of C)).Opens) ≤ ⊤
    from le_top)).op

theorem principal_naturality (c : C) (n : ℕ) : FrobeniusSections.map k C ⊤ n ≫ restrictionMap k C c n =
    FrobeniusSections.map k C (PrimeSpectrum.basicOpen c) n :=
  naturality k C (homOfLE (show (PrimeSpectrum.basicOpen c : (Spec (CommRingCat.of C)).Opens) ≤ ⊤
    from le_top)).op n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusSections
