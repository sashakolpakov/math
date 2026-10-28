import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenPushforwardAcyclic
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.ExtVanishing
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TermsAreSheaves
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains

/-! # Affine Cech Acyclic -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineCechAcyclic.FiniteAffineCechAcyclic

noncomputable section

/-! Every term of the actual finite affine Čech resolution of native differential forms is coefficient-Ext-acyclic. -/

open _root_.CategoryTheory Abelian Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]

local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _

theorem intersection_ext_subsingleton (U : X.left.Opens) (hU : IsAffineOpen U) (j q : ℕ) :
    Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      (Cech.IntersectionSheaf.CechIntersectionSheaf.sheaf R X.left ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j) U) (q + 1)) := by
  let Y := Affine.OpenResolution.AffineOpenResolution.openModel R X U
  let G := TopCat.Sheaf.pushforward (ModuleCat R) U.inclusion'
  let H := (extFunctor.{1} (q + 1) : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)ᵒᵖ ⥤
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X ⥤ AddCommGrpCat.{1}).obj (op (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X))
  have : Subsingleton (H.obj (G.obj ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j))) :=
    Affine.OpenPushforwardAcyclic.AffineOpenPushforwardAcyclic.ext_subsingleton R X U hU j q
  have : IsOpenImmersion (Affine.OpenResolution.AffineOpenResolution.inclusion R X U).left :=
    inferInstanceAs (IsOpenImmersion U.ι)
  let e : Cech.IntersectionSheaf.CechIntersectionSheaf.sheaf R X.left ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j) U ≅
      G.obj ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j) :=
    G.mapIso (OpenForms.OpenFormsSheaves.sheafIso (Affine.OpenResolution.AffineOpenResolution.inclusion R X U) j)
  exact (ConcreteCategory.bijective_of_isIso (H.mapIso e).hom).injective.subsingleton

theorem intersection_presheaf_ext_subsingleton (U : X.left.Opens) (hU : IsAffineOpen U) (j q : ℕ) :
    Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      (⟨AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersection R X.left ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j).obj U,
        Cech.IntersectionSheaf.CechIntersectionSheaf.isSheaf R X.left ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j) U⟩ :
          AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) (q + 1)) := by
  let F := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j
  let H := (extFunctor.{1} (q + 1) : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)ᵒᵖ ⥤
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X ⥤ AddCommGrpCat.{1}).obj (op (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X))
  have : Subsingleton (H.obj (Cech.IntersectionSheaf.CechIntersectionSheaf.sheaf R X.left F U)) :=
    intersection_ext_subsingleton R X U hU j q
  let e : Cech.IntersectionSheaf.CechIntersectionSheaf.sheaf R X.left F U ≅
      (⟨AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersection R X.left F.obj U, Cech.IntersectionSheaf.CechIntersectionSheaf.isSheaf R X.left F U⟩ :
        AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) :=
    ObjectProperty.isoMk _ (Cech.IntersectionSheaf.CechIntersectionSheaf.presheafIso R X.left F U)
  exact (ConcreteCategory.bijective_of_isIso (H.mapIso e).inv).injective.subsingleton

variable {ι : Type} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))

include hU in
theorem term_ext_subsingleton (j p q : ℕ) :
    Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      (Cech.TermsAreSheaves.CechTermsAreSheaves.termSheaf R X.left ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j) U p) (q + 1)) := by
  have : X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from X.hom]
    infer_instance
  apply ExtVanishing.FiniteExtVanishing.product
  intro t
  exact intersection_presheaf_ext_subsingleton R X (∏ᶜ (U ∘ t))
    (AlgebraicGeometry.SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU p t) j q

include hU in
theorem sheafComplex_ext_subsingleton (j p q : ℕ) :
    Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.sheafComplex R X.left U ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j).obj).X p)
        (q + 1)) := by
  let F := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j
  let H := (extFunctor.{1} (q + 1) : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)ᵒᵖ ⥤
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X ⥤ AddCommGrpCat.{1}).obj (op (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X))
  have : Subsingleton (H.obj (Cech.TermsAreSheaves.CechTermsAreSheaves.termSheaf R X.left F U p)) :=
    term_ext_subsingleton R X U hU j p q
  let e : Cech.TermsAreSheaves.CechTermsAreSheaves.termSheaf R X.left F U p ≅
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.sheafComplex R X.left U F.obj).X p :=
    ObjectProperty.isoMk _ ((Cech.TermsAreSheaves.CechTermsAreSheaves.termIso R X.left F U p) ≪≫
      isoSheafify (Opens.grothendieckTopology X.left) (Cech.TermsAreSheaves.CechTermsAreSheaves.isSheaf R X.left F U p))
  exact (ConcreteCategory.bijective_of_isIso (H.mapIso e).inv).injective.subsingleton

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineCechAcyclic.FiniteAffineCechAcyclic
