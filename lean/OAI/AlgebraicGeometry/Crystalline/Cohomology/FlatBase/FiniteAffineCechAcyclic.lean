import OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.AffineOpenPushforwardAcyclic
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ZariskiCechInjective
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.ExtVanishing
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains

/-! # Finite Affine Cech Acyclic -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.FiniteAffineCechAcyclic.FlatBaseFiniteAffineCechAcyclic

noncomputable section

/-! # Every term of the finite affine Čech resolution of ordinary forms is acyclic -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]

local instance coefficientExt : HasExt.{u + 1} (DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _

theorem intersection (U : X.left.Opens) (hU : IsAffineOpen U) (j q : ℕ) :
    Subsingleton (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((ZariskiOpenFunctor.ZariskiOpenPushforward.intersection R U).obj ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j))
      (q + 1)) := by
  let Y := AffineOpenResolution.FlatBaseAffineOpenResolution.openModel R X U
  let g : Y ⟶ X := AffineOpenResolution.FlatBaseAffineOpenResolution.inclusion R X U
  let : IsOpenImmersion g.left := inferInstanceAs (IsOpenImmersion U.ι)
  let G : DeRhamGlobalId.DeRhamGlobal.Sheaves R Y ⥤ DeRhamGlobalId.DeRhamGlobal.Sheaves R X :=
    TopCat.Sheaf.pushforward (ModuleCat.{u} R) U.inclusion'
  let : Subsingleton (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      (G.obj ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j)) (q + 1)) :=
    AffineOpenPushforwardAcyclic.FlatBaseAffineOpenPushforwardAcyclic.ext_subsingleton R X U hU j q
  let e : Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((ZariskiOpenFunctor.ZariskiOpenPushforward.intersection R U).obj ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j))
        (q + 1) ≃ₗ[R]
      Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) (G.obj ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j))
        (q + 1) :=
    SheafCohomology.Ext.Projective.extRightIso R (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      (G.mapIso (NumberTheory.PadicHodge.GeometricComparison.OpenForms.OpenFormsSheaves.sheafIso g j)) (q + 1)
  exact e.injective.subsingleton

variable {ι : Type u} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))

include hU in
theorem term (j p q : ℕ) :
    Subsingleton (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      (((MixedCech.Functor.MixedCechFunctor.sheafFunctor R X.left U).obj ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j)).X p)
      (q + 1)) := by
  have : X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from X.hom]
    infer_instance
  let F := (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j
  let T (t : Fin (p + 1) → ι) := (ZariskiOpenFunctor.ZariskiOpenPushforward.intersection R (∏ᶜ (U ∘ t))).obj F
  let : Subsingleton (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) (∏ᶜ T) (q + 1)) :=
    NumberTheory.PadicHodge.GeometricComparison.Finite.ExtVanishing.FiniteExtVanishing.product (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) T (q + 1)
      (fun t => intersection R X (∏ᶜ (U ∘ t)) (SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU p t) j q)
  exact (SheafCohomology.Ext.Projective.extRightIso R (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
    (ZariskiCechInjective.ZariskiCechTerms.termIso R X.left F U p) (q + 1)).injective.subsingleton

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.FiniteAffineCechAcyclic.FlatBaseFiniteAffineCechAcyclic
