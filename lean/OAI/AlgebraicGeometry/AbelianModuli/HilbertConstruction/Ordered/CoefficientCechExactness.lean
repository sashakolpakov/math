import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoefficientSectionExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CechIntersections
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Coefficient Cech Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechExactness

noncomputable section

/-!
# Exact sequences of ordered base-linear Cech complexes

This file proves that the ordered base-linear Cech complex on an affine family sends short exact
sequences of quasicoherent scheme modules to degreewise short exact sequences.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

universe u

private noncomputable def orderedCoefficientCechFunctorXIsoPi
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    ((CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).obj M).X n ≅
      ModuleCat.of R
        (∀ i : SectionCechIndices.OrderedCechIndex ι n,
          ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).obj M).obj
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k)))) :=
  CoefficientCechTerms.orderedCoefficientCechObjectIsoPi c M U n

@[simp]
private theorem orderedCoefficientCechFunctorXIsoPi_hom_apply
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (x : ((CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).obj M).X n)
    (i : SectionCechIndices.OrderedCechIndex ι n) :
    (orderedCoefficientCechFunctorXIsoPi c M U n).hom x i =
      Pi.π (fun j : SectionCechIndices.OrderedCechIndex ι n ↦
        ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).obj M).obj
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j.1 k)))) i x :=
  ModuleCat.piIsoPi_hom_ker_subtype_apply _ i x

private theorem orderedCoefficientCechFunctorXIsoPi_hom_map_apply
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (x : ((CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).obj M).X n)
    (i : SectionCechIndices.OrderedCechIndex ι n) :
    (orderedCoefficientCechFunctorXIsoPi c N U n).hom
        (((CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map f).f n x) i =
      (((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map f).app
        (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))))
        ((orderedCoefficientCechFunctorXIsoPi c M U n).hom x i) := by
  rw [orderedCoefficientCechFunctorXIsoPi_hom_apply,
    orderedCoefficientCechFunctorXIsoPi_hom_apply]
  exact ConcreteCategory.congr_hom
    (Limits.Pi.map_π (fun j : SectionCechIndices.OrderedCechIndex ι n ↦
      ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map f).app
        (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j.1 k)))) i) x

/-- A short exact sequence of quasicoherent scheme modules remains short exact after taking its
ordered base-linear Cech complexes on an affine family. -/
theorem orderedCoefficientCech_shortExact
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) [X.IsSeparated]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent] :
    (T.map (CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let A := (T.map (CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U)).map
    (HomologicalComplex.eval _ _ n)
  change A.ShortExact
  have hlocal (i : SectionCechIndices.OrderedCechIndex ι n) :=
    Affine.CoefficientSectionExactness.affine_coefficient_sections_shortExact
      c hT (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))
      (Affine.CechIntersections.affine_cechIntersection U hU n i.1)
  have : Mono A.f := by
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective (((CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map T.f).f n)
    intro x y hxy
    apply (ModuleCat.mono_iff_injective
      (orderedCoefficientCechFunctorXIsoPi c T.X₁ U n).hom).mp inferInstance
    funext i
    have hi := congrArg
      (fun z ↦ (orderedCoefficientCechFunctorXIsoPi c T.X₂ U n).hom z i) hxy
    rw [orderedCoefficientCechFunctorXIsoPi_hom_map_apply,
      orderedCoefficientCechFunctorXIsoPi_hom_map_apply] at hi
    exact (hlocal i).moduleCat_injective_f hi
  have : Epi A.g := by
    rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (((CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map T.g).f n)
    intro y
    have preimage (i : SectionCechIndices.OrderedCechIndex ι n) :
        ∃ x : ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).obj T.X₂).obj
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))),
          ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map T.g).app
              (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))) x =
            (orderedCoefficientCechFunctorXIsoPi c T.X₃ U n).hom y i :=
      (hlocal i).moduleCat_surjective_g _
    choose x hx using preimage
    let x' := (orderedCoefficientCechFunctorXIsoPi c T.X₂ U n).inv x
    refine ⟨x', ?_⟩
    apply (ModuleCat.mono_iff_injective
      (orderedCoefficientCechFunctorXIsoPi c T.X₃ U n).hom).mp inferInstance
    funext i
    rw [orderedCoefficientCechFunctorXIsoPi_hom_map_apply]
    have hx'i : (orderedCoefficientCechFunctorXIsoPi c T.X₂ U n).hom x' i = x i :=
      congrFun (Iso.inv_hom_id_apply
        (orderedCoefficientCechFunctorXIsoPi c T.X₂ U n) x) i
    rw [hx'i]
    exact hx i
  refine ShortComplex.ShortExact.mk ?_
  change ((T.map (CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U)).map
    (HomologicalComplex.eval _ _ n)).Exact
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  change ((CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).obj T.X₂).X n at y
  change (((CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map T.g).f n) y = 0 at hy
  have preimage (i : SectionCechIndices.OrderedCechIndex ι n) :
      ∃ x : ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).obj T.X₁).obj
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))),
        ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map T.f).app
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))) x =
          (orderedCoefficientCechFunctorXIsoPi c T.X₂ U n).hom y i := by
    have hyi :
        ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map T.g).app
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k)))
              ((orderedCoefficientCechFunctorXIsoPi c T.X₂ U n).hom y i) = 0 := by
      calc
        _ = (orderedCoefficientCechFunctorXIsoPi c T.X₃ U n).hom
            (((CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map T.g).f n y) i :=
          (orderedCoefficientCechFunctorXIsoPi_hom_map_apply c T.g U n y i).symm
        _ = 0 := by rw [hy, map_zero]; rfl
    exact ((ShortComplex.moduleCat_exact_iff _).mp (hlocal i).exact) _ hyi
  choose x hx using preimage
  let x' := (orderedCoefficientCechFunctorXIsoPi c T.X₁ U n).inv x
  refine ⟨x', ?_⟩
  change (((CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map T.f).f n) x' = y
  apply (ModuleCat.mono_iff_injective
    (orderedCoefficientCechFunctorXIsoPi c T.X₂ U n).hom).mp inferInstance
  funext i
  rw [orderedCoefficientCechFunctorXIsoPi_hom_map_apply]
  have hx'i : (orderedCoefficientCechFunctorXIsoPi c T.X₁ U n).hom x' i = x i :=
    congrFun (Iso.inv_hom_id_apply
      (orderedCoefficientCechFunctorXIsoPi c T.X₁ U n) x) i
  rw [hx'i]
  exact hx i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechExactness
