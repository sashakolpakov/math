import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubePointEvaluation

/-! # Pointed Global Constants -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PointedGlobalConstants

noncomputable section

/-! A rational point makes the global functions on a universally closed
integral scheme equal to its base field, without algebraic closure. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u

namespace Construction.CubeCech

variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
variable [IsIntegral X] [UniversallyClosed f]
variable (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)

include s hs

theorem globalConstants_bijective_of_point : Function.Bijective (CubeProperGlobalSections.Construction.CubeCech.globalConstants f) := by
  let : Field Γ(X, ⊤) := (isField_of_universallyClosed K f).toField
  let e := CubePointEvaluation.Construction.CubeCech.pointEvaluationRingHom s ⊤ le_top
  have he : ∀ r, e (CubeProperGlobalSections.Construction.CubeCech.globalConstants f r) = r := by
    intro r
    have htop : CubeSectionsAsAlgebra.Construction.CubeCech.sectionConstants f ⊤ = CubeProperGlobalSections.Construction.CubeCech.globalConstants f := by
      change (X.presheaf.map (𝟙 (op ⊤))).hom.comp (CubeProperGlobalSections.Construction.CubeCech.globalConstants f) = _
      rw [CategoryTheory.Functor.map_id]
      rfl
    rw [← htop]
    exact CubePointEvaluation.Construction.CubeCech.pointEvaluation_constants f s hs ⊤ le_top r
  refine ⟨(CubeProperGlobalSections.Construction.CubeCech.globalConstants f).injective, ?_⟩
  intro r
  exact ⟨e r, e.injective (he (e r))⟩

theorem properCechAugmentation_exact_of_point {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    Function.Exact (CubeProperCechAugmentation.Construction.CubeCech.properCechAugmentation f U)
      (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) := by
  intro x
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := (OpenCechDegreeZero.Construction.CubeCech.openModuleCech_exact_degreeZero (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U hU x).mp hx
    obtain ⟨r, hr⟩ := (globalConstants_bijective_of_point f s hs).surjective t
    exact ⟨r, (congrArg (OpenCechDegreeZero.Construction.CubeCech.openModuleCechUnit (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) hr).trans ht⟩
  · rintro ⟨r, rfl⟩
    exact (OpenCechDegreeZero.Construction.CubeCech.openModuleCech_exact_degreeZero (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U hU _).mpr
      ⟨CubeRelativeModuleSheaf.Construction.CubeCech.globalConstantsLinearMap f r, rfl⟩

end Construction.CubeCech

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PointedGlobalConstants
