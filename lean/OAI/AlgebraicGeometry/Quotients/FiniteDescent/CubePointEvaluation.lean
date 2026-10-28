import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeSectionsAsAlgebra
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProperCechAugmentation

/-! # Cube Point Evaluation -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubePointEvaluation.Construction.CubeCech

noncomputable section

/-! Evaluation at a rational point splits the constant functions in Cech degree zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u v

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _)

def pointEvaluationRingHom (U : X.Opens) (hU : ⊤ ≤ s ⁻¹ᵁ U) : Γ(X, U) →+* k :=
  (s.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (.of k)).hom).hom

include hs in
theorem pointEvaluation_constants (U : X.Opens) (hU : ⊤ ≤ s ⁻¹ᵁ U) (r : k) :
    pointEvaluationRingHom s U hU (CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants f U r) = r := by
  have h := RingHom.congr_fun (CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants_pullback f s U ⊤ hU) r
  have h' := congrArg (fun x ↦ (Scheme.ΓSpecIso (.of k)).hom x) h
  change pointEvaluationRingHom s U hU (CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants f U r) =
    (Scheme.ΓSpecIso (.of k)).hom (CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants (s ≫ f) ⊤ r) at h'
  rw [hs] at h'
  refine h'.trans ?_
  simp [CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants, CubeProperGlobalSections.Construction.CubeCech.globalConstants]

def pointEvaluationAlgHom (U : X.Opens) (hU : ⊤ ≤ s ⁻¹ᵁ U) :
    CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseAlgebra f U →ₐ[k] k where
  __ := pointEvaluationRingHom s U hU
  commutes' r := pointEvaluation_constants f s hs U hU r

def pointEvaluationLinearMap (U : X.Opens) (hU : ⊤ ≤ s ⁻¹ᵁ U) :
    (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U) →ₗ[k] k :=
  (pointEvaluationAlgHom f s hs U hU).toLinearMap.comp
    (CubeSectionsAsAlgebra.Construction.CubeCech.sectionsAsBaseModuleIso f U).toLinearEquiv.symm.toLinearMap

def pointCechRetraction {ι : Type v} (U : ι → X.Opens) (i : ι) (hi : ⊤ ≤ s ⁻¹ᵁ U i) :
    OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U →ₗ[k] k :=
  (pointEvaluationLinearMap f s hs (U i) hi).comp (LinearMap.proj i)

theorem pointCechRetraction_comp {ι : Type v} (U : ι → X.Opens) (i : ι)
    (hi : ⊤ ≤ s ⁻¹ᵁ U i) :
    (pointCechRetraction f s hs U i hi).comp (CubeProperCechAugmentation.Construction.CubeCech.properCechAugmentation f U) = LinearMap.id := by
  apply LinearMap.ext
  intro r
  exact pointEvaluation_constants f s hs (U i) hi r

theorem pointCech_index_exists {ι : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    ∃ i, ⊤ ≤ s ⁻¹ᵁ U i := by
  let p : Spec (.of k) := IsLocalRing.closedPoint k
  have hp : s p ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  refine ⟨i, ?_⟩
  intro x _
  have hx : x = p := Subsingleton.elim _ _
  change s x ∈ U i
  rw [hx]
  exact hi

def chosenPointCechRetraction {ι : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U →ₗ[k] k :=
  pointCechRetraction f s hs U (pointCech_index_exists s U hU).choose
    (pointCech_index_exists s U hU).choose_spec

theorem chosenPointCechRetraction_comp {ι : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    (chosenPointCechRetraction f s hs U hU).comp (CubeProperCechAugmentation.Construction.CubeCech.properCechAugmentation f U) = LinearMap.id :=
  pointCechRetraction_comp f s hs U _ _

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubePointEvaluation.Construction.CubeCech
