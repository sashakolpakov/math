import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ZariskiExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Image
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-! # Cohomology Cover Module -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CohomologyCoverModule.ZariskiCohomology

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

/-- A finite product of quasicoherent modules on an affine spectrum is
quasicoherent. -/
theorem moduleSpec_isQuasicoherent_pi {R : CommRingCat.{u}}
    {I : Type u} [Finite I] (F : I → (Spec R).Modules)
    [∀ i, (F i).IsQuasicoherent] :
    (∏ᶜ F).IsQuasicoherent := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let : P.IsClosedUnderLimitsOfShape (Discrete I) := by
    change (SheafOfModules.isQuasicoherent
      (Spec R).ringCatSheaf).IsClosedUnderLimitsOfShape (Discrete I)
    rw [← AlgebraicGeometry.essImage_tilde]
    have : HasLimitsOfShape (Discrete I) (ModuleCat R) := inferInstance
    have : PreservesLimitsOfShape (Discrete I) (tilde.functor R) :=
      inferInstance
    exact
    instIsClosedUnderLimitsOfShapeEssImageOfHasLimitsOfShapeOfPreservesLimitsOfShapeOfFullOfFaithful
      (tilde.functor R)
  exact P.prop_limit (Discrete.functor F) (fun i ↦
    inferInstanceAs ((F i.as).IsQuasicoherent))

/-- The finite-cover module formed from restriction-pushforwards. -/
noncomputable def affineCoverModule {R : CommRingCat.{u}} {I : Type u}
    (M : (Spec R).Modules) (U : I → (Spec R).Opens) :
    (Spec R).Modules :=
  ∏ᶜ fun i ↦
    (Scheme.Modules.restrictFunctor (U i).ι ⋙
      Scheme.Modules.pushforward (U i).ι).obj M

/-- The adjunction units map a module into its finite-cover module. -/
noncomputable def toAffineCoverModule {R : CommRingCat.{u}} {I : Type u}
    (M : (Spec R).Modules) (U : I → (Spec R).Opens) :
    M ⟶ affineCoverModule M U :=
  Pi.lift fun i ↦ (Scheme.Modules.restrictAdjunction (U i).ι).unit.app M

@[simp]
theorem toAffineCoverModule_comp_pi {R : CommRingCat.{u}} {I : Type u}
    (M : (Spec R).Modules) (U : I → (Spec R).Opens) (i : I) :
    toAffineCoverModule M U ≫
      Pi.π (fun i ↦
        (Scheme.Modules.restrictFunctor (U i).ι ⋙
          Scheme.Modules.pushforward (U i).ι).obj M) i =
      (Scheme.Modules.restrictAdjunction (U i).ι).unit.app M := by
  simp [toAffineCoverModule, affineCoverModule]

/-- A finite affine restriction-pushforward cover module on an affine
spectrum is quasicoherent. -/
theorem affineCoverModule_isQuasicoherent {R : CommRingCat.{u}}
    {I : Type u} [Finite I] (M : (Spec R).Modules)
    [M.IsQuasicoherent] (U : I → (Spec R).Opens)
    [∀ i, IsAffine (U i)] :
    (affineCoverModule M U).IsQuasicoherent := by
  let (i : I) :
      ((Scheme.Modules.restrictFunctor (U i).ι).obj M).IsQuasicoherent :=
    inferInstance
  let (i : I) :
      ((Scheme.Modules.restrictFunctor (U i).ι ⋙
        Scheme.Modules.pushforward (U i).ι).obj M).IsQuasicoherent := by
    change ((Scheme.Modules.pushforward (U i).ι).obj
      ((Scheme.Modules.restrictFunctor (U i).ι).obj M)).IsQuasicoherent
    exact Quasicoherent.Image.quasiCompact_separated_directImage_affine (U i).ι _
  exact moduleSpec_isQuasicoherent_pi _

/-- The ambient cokernel of the finite-cover map is quasicoherent. This is
the finite-cover downstream consumer of affine cokernel closure. -/
theorem affineCoverCokernel_isQuasicoherent {R : CommRingCat.{u}}
    {I : Type u} [Finite I] (M : (Spec R).Modules)
    [M.IsQuasicoherent] (U : I → (Spec R).Opens)
    [∀ i, IsAffine (U i)] :
    (cokernel (toAffineCoverModule M U)).IsQuasicoherent := by
  let : (affineCoverModule M U).IsQuasicoherent :=
    affineCoverModule_isQuasicoherent M U
  exact ZariskiExactness.ZariskiCohomology.moduleSpec_isQuasicoherent_cokernel (toAffineCoverModule M U)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CohomologyCoverModule.ZariskiCohomology
