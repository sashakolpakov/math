import OAI.AlgebraicGeometry.Comparison.Betti.Cech.PushforwardCoordinates
import OAI.AlgebraicTopology.DeRham.Comparison.CechTotalFunctor

/-! # Pushforward Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.PushforwardFunctor

noncomputable section

/-! The Čech direct-image identification is natural and extends to both degrees of a total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)

abbrev presheafDirectImage :
    ((Opens Y)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ⥤ ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) :=
  (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens Y)ᵒᵖ (ModuleCat.{0} ℂ)).obj (Opens.map f).op

theorem cechPushforwardSectionIso_naturality
    {F G : (Opens Y)ᵒᵖ ⥤ ModuleCat.{0} ℂ} (α : F ⟶ G) {n : ℕ} (a : Fin (n + 1) → ι) :
    α.app (op ((Opens.map f).obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))) ≫
        (PushforwardCoordinates.cechPushforwardSectionIso f U G a).hom =
      (PushforwardCoordinates.cechPushforwardSectionIso f U F a).hom ≫
        α.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (Opens.map f).obj (U i)) a)) :=
  (α.naturality (eqToHom (congrArg op (PushforwardCoordinates.cechIntersection_preimage f U a)))).symm

def cechPushforwardFunctorIso :
    presheafDirectImage f ⋙ AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechComplexFunctor U ≅
      AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechComplexFunctor (fun i => (Opens.map f).obj (U i)) :=
  NatIso.ofComponents (fun F => PushforwardCoordinates.cechPushforwardComplexIso f U F) (fun α => by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    exact ConcreteCategory.congr_hom (cechPushforwardSectionIso_naturality f U α a) (x a))

def presheafDirectImageComplex
    (K : CochainComplex ((Opens Y)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ) :
    CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ :=
  ((presheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj K

def cechPushforwardBicomplexIso
    (K : CochainComplex ((Opens Y)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ) :
    AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex U (presheafDirectImageComplex f K) ≅
      AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex (fun i => (Opens.map f).obj (U i)) K :=
  (HomologicalComplex₂.flipFunctor (ModuleCat.{0} ℂ) (.up ℕ) (.up ℕ)).mapIso
    ((NatIso.mapHomologicalComplex (cechPushforwardFunctorIso f U) (.up ℕ)).app K)

def cechPushforwardTotalIso
    (K : CochainComplex ((Opens Y)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ) :
    AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalComplex U (presheafDirectImageComplex f K) ≅
      AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalComplex (fun i => (Opens.map f).obj (U i)) K :=
  HomologicalComplex₂.total.mapIso (cechPushforwardBicomplexIso f U K) (.up ℕ)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.PushforwardFunctor
