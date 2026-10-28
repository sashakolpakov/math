import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoordinateNonvanishing

/-! # Function Nonvanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.FunctionNonvanishing

noncomputable section

/-! The frame-section nonvanishing formula stated directly using regular functions on the ambient chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)
variable (s : Line.Bundles.structureModule X ⟶ ModuleSheaf.openFrameModuleSheaf D) (k : ι)

theorem openFrameSection_nonvanishing_chart_function :
    (U k).ι ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing s =
      (U k).ι ⁻¹ᵁ X.basicOpen (show Γ(X, U k) from CoefficientSections.openFrameGlobalTupleMap D
        (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D) s) k) := by
  let r : Γ(X, U k) := CoefficientSections.openFrameGlobalTupleMap D
    (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D) s) k
  have h : (⊤ : (U k).toScheme.Opens) ≤ (U k).ι ⁻¹ᵁ U k := by
    intro x _
    exact x.property
  have hc : CoordinateNonvanishing.openFrameChartCoordinate D s k = (U k).ι.appLE (U k) ⊤ h r := by
    rw [Scheme.Opens.ι_appLE]
    simp only [CoordinateNonvanishing.openFrameChartCoordinate, Scheme.Opens.ι_appIso]
    rfl
  have hb : (U k).toScheme.basicOpen ((U k).ι.appLE (U k) ⊤ h r) =
      (U k).ι ⁻¹ᵁ X.basicOpen r := by
    exact (Scheme.basicOpen_appLE (U k).ι ⊤ (U k) h r).trans (inf_eq_right.mpr le_top)
  exact (CoordinateNonvanishing.openFrameSection_nonvanishing_on_chart D s k).trans
    ((congrArg (fun a : Γ((U k).toScheme, ⊤) => (U k).toScheme.basicOpen a) hc).trans hb)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.FunctionNonvanishing
