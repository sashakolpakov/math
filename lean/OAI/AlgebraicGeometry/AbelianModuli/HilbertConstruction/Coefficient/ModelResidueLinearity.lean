import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModelFirstCycles

/-! # Model Residue Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModelResidueLinearity

noncomputable section

/-! For surjective coefficient changes, the actual model's first-cycle/section comparison is linear over the final coefficient ring. In particular, the first rank of a local minimal model equals the dimension of the actual residue-fiber sections over the residue field. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
section

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

def baseChangeFirstCyclesTensorLinearEquiv (D : CochainComplex (ModuleCat.{u} R) ℕ) :
    LinearMap.ker ((D.d 0 1).hom.baseChange B) ≃ₗ[R]
      LinearMap.ker ((HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex B D).d 0 1).hom where
  __ := ModelFirstCycles.baseChangeFirstCyclesTensorEquiv (B := B) D
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private theorem coefficientSections_scalar_of_comp
    {Y : Scheme.{u}} (L : Y.Modules) (q : B →+* Γ(Y, ⊤)) (c : R →+* Γ(Y, ⊤))
    (hq : q.comp (algebraMap R B) = c) (r : R)
    (x : (ModulePresheaf.coefficientModulePresheaf q L).obj (op ⊤)) :
    (algebraMap R B r) • x =
      (show (ModulePresheaf.coefficientModulePresheaf q L).obj (op ⊤) from
        r • (show (ModulePresheaf.coefficientModulePresheaf c L).obj (op ⊤) from x)) := by
  change q (algebraMap R B r) • (show (Global.RingModulePresheaf.globalRingModulePresheaf L).obj (op ⊤) from x) =
    c r • (show (Global.RingModulePresheaf.globalRingModulePresheaf L).obj (op ⊤) from x)
  exact congrArg (fun z : Γ(Y, ⊤) => z •
    (show (Global.RingModulePresheaf.globalRingModulePresheaf L).obj (op ⊤) from x)) (DFunLike.congr_fun hq r)

variable {X Y : Scheme.{u}} (a : Y ⟶ X) (c : R →+* Γ(X, ⊤)) (M : X.Modules)
variable (q : B →+* Γ(Y, ⊤)) (hq : q.comp (algebraMap R B) = a.appTop.hom.comp c)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} R) ℕ}
variable (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U)
variable [hψ : QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫
  SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a c M q hq U) 0]

def coefficientCechModelFirstCyclesRLinearEquiv :
    LinearMap.ker ((D.d 0 1).hom.baseChange B) ≃ₗ[R]
      (ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp c) ((Scheme.Modules.pullback a).obj M)).obj (op ⊤) := by
  let L := (Scheme.Modules.pullback a).obj M
  let N := (Scheme.Modules.pushforward a).obj L
  let ψ := HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a c M q hq U
  have : QuasiIsoAt ψ 0 := hψ
  exact (baseChangeFirstCyclesTensorLinearEquiv (B := B) D).trans
    ((Cech.ModelGlobalSections.CechModelSections.equiv c N U hU ψ).trans (PushforwardModuleComparison.coefficientPushforwardModuleComponent a c L ⊤))

def coefficientCechModelFirstCyclesLinearEquiv
    (hs : Function.Surjective (algebraMap R B)) :
    LinearMap.ker ((D.d 0 1).hom.baseChange B) ≃ₗ[B]
      (ModulePresheaf.coefficientModulePresheaf q ((Scheme.Modules.pullback a).obj M)).obj (op ⊤) := by
  let L := (Scheme.Modules.pullback a).obj M
  let V := LinearMap.ker ((D.d 0 1).hom.baseChange B)
  let WR := (ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp c) L).obj (op ⊤)
  let WB := (ModulePresheaf.coefficientModulePresheaf q L).obj (op ⊤)
  let e : V ≃ₗ[R] WR := coefficientCechModelFirstCyclesRLinearEquiv a c M q hq U hU φ
  refine {
    toFun := fun x => e x
    invFun := fun y => e.symm y
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := fun x y => e.map_add x y
    map_smul' := ?_ }
  intro b x
  obtain ⟨r, rfl⟩ := hs b
  have hx : (algebraMap R B r) • x = r • x :=
    IsScalarTower.algebraMap_smul (R := R) (M := V) B r x
  have he : (show WB from e (r • x)) = (show WB from r • e x) :=
    congrArg (fun w : WR => (show WB from w)) (e.map_smul r x)
  exact (congrArg (fun v : V => (show WB from e v)) hx).trans
    (he.trans (coefficientSections_scalar_of_comp L q (a.appTop.hom.comp c) hq r (e x)).symm)

end

theorem minimal_firstModule_finrank_eq_residue_sections
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    (q : IsLocalRing.ResidueField R →+* Γ(Y, ⊤))
    (hq : q.comp (algebraMap R (IsLocalRing.ResidueField R)) = a.appTop.hom.comp c)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} R) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U)
    [QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (IsLocalRing.ResidueField R) φ ≫
      SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a c M q hq U) 0]
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (D.sc' 0 1 2)) :
    Module.finrank R Q.complex.X₁ = Module.finrank (IsLocalRing.ResidueField R)
      ((ModulePresheaf.coefficientModulePresheaf q ((Scheme.Modules.pullback a).obj M)).obj (op ⊤)) := by
  have hs : Function.Surjective (algebraMap R (IsLocalRing.ResidueField R)) := by
    simpa only [IsLocalRing.ResidueField.algebraMap_eq] using (IsLocalRing.residue_surjective (R := R))
  exact Q.first_finrank_eq_residue_cycles.trans
    (coefficientCechModelFirstCyclesLinearEquiv a c M q hq U hU φ hs).finrank_eq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModelResidueLinearity
