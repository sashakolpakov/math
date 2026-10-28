import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperIntegral
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Proper Birational -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperBirational.Construction.ProperBirationalFunctions

/-! A proper reduced scheme with a dense rational lift of the generic
point of a normal affine base has exactly the functions of that base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperIntegral.Construction.ProperIntegralFunctions

theorem isIso_scalarMap
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (g : Spec (.of K) ⟶ X) [IsDominant g]
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    IsIso (ProperIntegral.Construction.ProperIntegralFunctions.scalarMap f) := by
  let e : Γ(X, ⊤) ⟶ CommRingCat.of K :=
    g.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom
  have hce : ProperIntegral.Construction.ProperIntegralFunctions.scalarMap f ≫ e = CommRingCat.ofHom (algebraMap R K) := by
    calc
      ProperIntegral.Construction.ProperIntegralFunctions.scalarMap f ≫ e = (Scheme.ΓSpecIso (.of R)).inv ≫
          (g ≫ f).appTop ≫ (Scheme.ΓSpecIso (.of K)).hom := by
        simp only [ProperIntegral.Construction.ProperIntegralFunctions.scalarMap, e, Scheme.Hom.comp_appTop, Category.assoc]
      _ = _ := by
        rw [hg, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have : IsSchemeTheoreticallyDominant g := .of_isDominant g
  have : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from f]
    infer_instance⟩
  have he : Function.Injective e :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).hom).1.comp
      (g.app_injective ⊤)
  have hc : Function.Injective (ProperIntegral.Construction.ProperIntegralFunctions.scalarMap f) := by
    intro a b hab
    apply IsFractionRing.injective R K
    have hh := congrArg (fun t : CommRingCat.of R ⟶ CommRingCat.of K => t a) hce
    have hh' := congrArg (fun t : CommRingCat.of R ⟶ CommRingCat.of K => t b) hce
    exact hh.symm.trans ((congrArg e hab).trans hh')
  have hs : Function.Surjective (ProperIntegral.Construction.ProperIntegralFunctions.scalarMap f) := by
    intro a
    have ha := (ProperIntegral.Construction.ProperIntegralFunctions.isIntegral f a).map e.hom
    have hc' : e.hom.comp (ProperIntegral.Construction.ProperIntegralFunctions.scalarMap f).hom = algebraMap R K :=
      congrArg CommRingCat.Hom.hom hce
    rw [hc'] at ha
    obtain ⟨r, hr⟩ := (isIntegrallyClosed_iff K).mp ‹IsIntegrallyClosed R› ha
    refine ⟨r, he ?_⟩
    exact (congrArg (fun t : CommRingCat.of R ⟶ CommRingCat.of K => t r) hce).trans hr
  exact (ConcreteCategory.isIso_iff_bijective (ProperIntegral.Construction.ProperIntegralFunctions.scalarMap f)).mpr ⟨hc, hs⟩

theorem isIso_appTop
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (g : Spec (.of K) ⟶ X) [IsDominant g]
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    IsIso f.appTop := by
  have hi := isIso_scalarMap f g hg
  change IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) at hi
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of R)).inv f.appTop

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperBirational.Construction.ProperBirationalFunctions
