import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionTensorModelCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardModuleComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ResidueSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.DegreeZero

/-! # Model First Cycles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModelFirstCycles

noncomputable section

/-! The first cycles of the actual coefficient-changed model are the actual global sections on the pulled-back scheme. The B-linear and R-linear tensor differentials are compared through their identical underlying functions. These identifications transfer vanishing and nontriviality without changing scalar actions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
section

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

def baseChangeFirstCyclesTensorEquiv (D : CochainComplex (ModuleCat.{u} R) ℕ) :
    LinearMap.ker (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B (D.sc' 0 1 2)).f.hom ≃
      LinearMap.ker ((Module.TensorFunctor.ModuleTensorFunctor.complex B D).d 0 1).hom where
  toFun x := ⟨x.val, by
    have he := congrFun (LinearMap.baseChange_eq_ltensor (A := B) (D.d 0 1).hom) x.val
    exact he.symm.trans x.property⟩
  invFun x := ⟨x.val, by
    have he := congrFun (LinearMap.baseChange_eq_ltensor (A := B) (D.d 0 1).hom) x.val
    exact he.trans x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

variable {X Y : Scheme.{u}} (a : Y ⟶ X) (c : R →+* Γ(X, ⊤)) (M : X.Modules)
variable (q : B →+* Γ(Y, ⊤)) (hq : q.comp (algebraMap R B) = a.appTop.hom.comp c)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} R) ℕ}
variable (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U)
variable [hψ : QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫
  SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a c M q hq U) 0]

def coefficientCechModelFirstCyclesEquiv :
    LinearMap.ker (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B (D.sc' 0 1 2)).f.hom ≃
      Γ((Scheme.Modules.pullback a).obj M, ⊤) := by
  let L := (Scheme.Modules.pullback a).obj M
  let N := (Scheme.Modules.pushforward a).obj L
  let ψ := Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a c M q hq U
  have : QuasiIsoAt ψ 0 := hψ
  let e : ((Module.TensorFunctor.ModuleTensorFunctor.complex B D).d 0 1).hom.ker ≃ₗ[R]
      (ModulePresheaf.coefficientModulePresheaf c N).obj (op ⊤) := Cech.ModelGlobalSections.CechModelSections.equiv c N U hU ψ
  let t : (ModulePresheaf.coefficientModulePresheaf c N).obj (op ⊤) ≃ Γ(L, ⊤) :=
    (PushforwardModuleComparison.coefficientPushforwardModuleComponent a c L ⊤).toEquiv
  exact (baseChangeFirstCyclesTensorEquiv (B := B) D).trans (e.toEquiv.trans t)

include hψ hU in
theorem coefficientCechModel_firstCycles_subsingleton
    (hs : Subsingleton Γ((Scheme.Modules.pullback a).obj M, ⊤)) :
    Subsingleton (LinearMap.ker
      (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B (D.sc' 0 1 2)).f.hom) := by
  let e := coefficientCechModelFirstCyclesEquiv a c M q hq U hU φ
  exact ⟨fun x y => e.injective (hs.elim (e x) (e y))⟩

include hψ hU in
theorem coefficientCechModel_firstCycles_subsingleton_of_cohomology_zero
    (hH : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H ((Scheme.Modules.pullback a).obj M) 0)) :
    Subsingleton (LinearMap.ker
      (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B (D.sc' 0 1 2)).f.hom) := by
  let L := (Scheme.Modules.pullback a).obj M
  let cY := a.appTop.hom.comp c
  let e : (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor cY 0).obj L ≃ Γ(L, ⊤) :=
    (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv cY L).toEquiv.trans
      (Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso cY L).toEquiv
  have hs : Subsingleton Γ(L, ⊤) := ⟨fun x y => e.symm.injective (hH.elim _ _)⟩
  exact coefficientCechModel_firstCycles_subsingleton a c M q hq U hU φ hs

end

theorem minimal_firstModule_nontrivial_of_residue_sections
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    (q : IsLocalRing.ResidueField R →+* Γ(Y, ⊤))
    (hq : q.comp (algebraMap R (IsLocalRing.ResidueField R)) = a.appTop.hom.comp c)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} R) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U)
    [QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (IsLocalRing.ResidueField R) φ ≫
      SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a c M q hq U) 0]
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (D.sc' 0 1 2))
    [Nontrivial Γ((Scheme.Modules.pullback a).obj M, ⊤)] : Nontrivial Q.complex.X₁ := by
  let e := (coefficientCechModelFirstCyclesEquiv a c M q hq U hU φ).symm.trans
    Q.residueFirstCyclesEquiv.toEquiv
  rcases subsingleton_or_nontrivial Q.complex.X₁ with h | h
  · have : Subsingleton Q.complex.X₁ := h
    have hs : Subsingleton (IsLocalRing.ResidueField R ⊗[R] Q.complex.X₁) := inferInstance
    obtain ⟨x, y, hxy⟩ := exists_pair_ne Γ((Scheme.Modules.pullback a).obj M, ⊤)
    exact False.elim (hxy (e.injective (hs.elim (e x) (e y))))
  · exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModelFirstCycles
