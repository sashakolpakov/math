import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafificationLocalIso

/-! # Line Bundle Evaluation -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleEvaluation.Construction

noncomputable section

/-! Evaluation identifies the tensor product of a line bundle and its dual with the unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

local instance lineBundleEvaluationMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

local instance lineBundleEvaluationSectionsModule {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (.op U)) := (M.val.obj (.op U)).isModule

def overTrivializationSectionLinearEquiv {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens}
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (hVU : V ≤ U) :
    M.val.obj (.op V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  ((SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (.op (Over.mk (homOfLE hVU)))).mapIso e).toLinearEquiv

theorem localHomEvaluation_coordinate {X : Scheme.{u}} {M N : X.Modules} {U V : X.Opens}
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (hVU : V ≤ U)
    (q : (SheafHomModule.Construction.sheafHomModule M N).val.obj (.op V)) (m : M.val.obj (.op V)) :
    overTrivializationSectionLinearEquiv eN hVU (SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N V q m) =
      HomLocalTrivialization.Construction.localHomCoordinateLinearEquiv eM eN V hVU q * overTrivializationSectionLinearEquiv eM hVU m := by
  let a := overTrivializationSectionLinearEquiv eM hVU
  let b := overTrivializationSectionLinearEquiv eN hVU
  let t := SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N V q
  let g := a.symm (1 : Γ(X, V))
  have hm : m = a m • g := by
    calc
      m = a.symm (a m) := (a.symm_apply_apply m).symm
      _ = a.symm (a m • (1 : Γ(X, V))) := by rw [smul_eq_mul, mul_one]
      _ = a m • g := a.symm.map_smul _ _
  have hc : HomLocalTrivialization.Construction.localHomCoordinateLinearEquiv eM eN V hVU q = b (t g) := rfl
  have ht : b (t m) = a m * b (t g) :=
    (congrArg (fun z ↦ b (t z)) hm).trans
      ((congrArg b (t.map_smul (a m) g)).trans (b.map_smul (a m) (t g)))
  exact ht.trans ((mul_comm (a m) (b (t g))).trans
    (congrArg (fun c ↦ c * a m) hc.symm))

def lineBundleEvaluationLinearEquiv {X : Scheme.{u}} {M N : X.Modules} {U V : X.Opens}
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (hVU : V ≤ U) :
    TensorProduct Γ(X, V) ((SheafHomModule.Construction.sheafHomModule M N).val.obj (.op V)) (M.val.obj (.op V)) ≃ₗ[Γ(X, V)]
      N.val.obj (.op V) :=
  (TensorProduct.congr (HomLocalTrivialization.Construction.localHomCoordinateLinearEquiv eM eN V hVU)
    (overTrivializationSectionLinearEquiv eM hVU)).trans
      ((TensorProduct.lid Γ(X, V) Γ(X, V)).trans (overTrivializationSectionLinearEquiv eN hVU).symm)

theorem lineBundleEvaluationLinearEquiv_eq {X : Scheme.{u}} {M N : X.Modules} {U V : X.Opens}
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (hVU : V ≤ U) :
    (lineBundleEvaluationLinearEquiv eM eN hVU).toLinearMap =
      TensorProduct.lift (SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N V) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro q
  apply LinearMap.ext
  intro m
  change lineBundleEvaluationLinearEquiv eM eN hVU (TensorProduct.tmul Γ(X, V) q m) =
    SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N V q m
  apply (overTrivializationSectionLinearEquiv eN hVU).injective
  change overTrivializationSectionLinearEquiv eN hVU
      ((overTrivializationSectionLinearEquiv eN hVU).symm
        (HomLocalTrivialization.Construction.localHomCoordinateLinearEquiv eM eN V hVU q * overTrivializationSectionLinearEquiv eM hVU m)) = _
  exact ((overTrivializationSectionLinearEquiv eN hVU).apply_symm_apply _).trans
    (localHomEvaluation_coordinate eM eN hVU q m).symm

theorem isIso_sheafHomEvalPresheaf_app {X : Scheme.{u}} {M N : X.Modules} {U V : X.Opens}
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (hVU : V ≤ U) :
    IsIso ((SheafHomEvaluation.Construction.sheafHomEvalPresheaf M N).app (.op V)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (TensorProduct.lift (SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N V))
  rw [← lineBundleEvaluationLinearEquiv_eq eM eN hVU]
  exact (lineBundleEvaluationLinearEquiv eM eN hVU).bijective

theorem isIso_sheafHomEvaluation_of_isLineBundle {X : Scheme.{u}} {M N : X.Modules}
    (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) : IsIso (SheafHomEvaluation.Construction.sheafHomEvaluation M N) := by
  have he : SheafificationLocalIso.Construction.moduleSheafificationLift (SheafHomEvaluation.Construction.sheafHomEvalPresheaf M N) = SheafHomEvaluation.Construction.sheafHomEvaluation M N := by
    apply (SheafTensor.Construction.sheafTensorHomEquiv _ _ _).injective
    exact (TensorUnit.Construction.sheafTensorHomEquiv_apply_eq (SheafificationLocalIso.Construction.moduleSheafificationLift (SheafHomEvaluation.Construction.sheafHomEvalPresheaf M N))).trans
      ((SheafificationLocalIso.Construction.moduleSheafificationUnit_lift (SheafHomEvaluation.Construction.sheafHomEvalPresheaf M N)).trans
        (SheafHomEvaluation.Construction.sheafHomEvaluation_homEquiv M N).symm)
  rw [← he]
  apply SheafificationLocalIso.Construction.isIso_moduleSheafificationLift_of_local_app
  intro x
  obtain ⟨U, hxU, ⟨eM⟩⟩ := hM x
  obtain ⟨V, hxV, ⟨eN⟩⟩ := hN x
  let W := U ⊓ V
  let a := LineBundleQuasicoherent.Construction.lineBundleOverTrivialization W (TensorRestriction.Construction.restrictLineBundleTrivialization inf_le_left eM)
  let b := LineBundleQuasicoherent.Construction.lineBundleOverTrivialization W (TensorRestriction.Construction.restrictLineBundleTrivialization inf_le_right eN)
  exact ⟨W, ⟨hxU, hxV⟩, fun _ h ↦ isIso_sheafHomEvalPresheaf_app a b h⟩

def lineBundleHomEvaluationIso {X : Scheme.{u}} {M N : X.Modules}
    (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) :
    SheafTensor.Construction.sheafTensor (SheafHomModule.Construction.sheafHomModule M N) M ≅ N := by
  have := isIso_sheafHomEvaluation_of_isLineBundle hM hN
  exact asIso (SheafHomEvaluation.Construction.sheafHomEvaluation M N)

def lineBundleDualTensorIso {X : Scheme.{u}} {M : X.Modules} (hM : LineBundle.Construction.IsLineBundle M) :
    SheafTensor.Construction.sheafTensor (SheafHomModule.Construction.lineBundleDual M) M ≅ LineBundle.Construction.structureSheafModule X :=
  lineBundleHomEvaluationIso hM (LineBundle.Construction.isLineBundle_structureSheaf X)

def lineBundleTensorDualIso {X : Scheme.{u}} {M : X.Modules} (hM : LineBundle.Construction.IsLineBundle M) :
    SheafTensor.Construction.sheafTensor M (SheafHomModule.Construction.lineBundleDual M) ≅ LineBundle.Construction.structureSheafModule X :=
  SheafTensor.Construction.sheafTensorComm M (SheafHomModule.Construction.lineBundleDual M) ≪≫ lineBundleDualTensorIso hM

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleEvaluation.Construction
