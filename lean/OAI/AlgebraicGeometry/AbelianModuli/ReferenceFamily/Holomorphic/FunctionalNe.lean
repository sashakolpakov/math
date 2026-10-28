import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AnalytificationUnit
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HolomorphicLineMorphismAlgebraization

/-! # Functional Ne -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.FunctionalNe

/-! Actual algebraic module maps into the direct image of the native
holomorphic structure module, with literal section and scalar formulas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AnalytificationUnit

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

abbrev HolomorphicScalarFunctional (M : V.carrier.Modules) :=
  M ⟶ (DivisorClass.Chern.Holomorphic.ModuleAnalytification.holomorphicModuleDirectImage V).obj
    (SheafOfModules.unit (DivisorClass.Chern.HolomorphicSection.Modules.holomorphicStructureRingSheaf V.analyticModel V.analyticSpace))

namespace HolomorphicScalarFunctional

variable {V} {M : V.carrier.Modules} (f : HolomorphicScalarFunctional V M)

def onSection (U : V.carrier.Opens) (z : Γ(M, U)) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U) :=
  f.app U z

theorem section_add (U : V.carrier.Opens) (z w : Γ(M, U)) :
    f.onSection U (z + w) = f.onSection U z + f.onSection U w := by
  exact (HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp f U).map_add z w

theorem section_smul (U : V.carrier.Opens) (a : Γ(V.carrier, U)) (z : Γ(M, U)) :
    f.onSection U (a • z) = DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V U a * f.onSection U z := by
  exact (HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp f U).map_smul a z

theorem section_restrict {U W : V.carrier.Opens} (h : W ≤ U) (z : Γ(M, U)) :
    f.onSection W (M.presheaf.map (homOfLE h).op z) =
      DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction (show DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W ≤
        DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U from fun _ hx => h hx) (f.onSection U z) := by
  exact ConcreteCategory.congr_hom (f.mapPresheaf.naturality (homOfLE h).op) z

theorem section_value_restrict {U W : V.carrier.Opens} (h : W ≤ U) (z : Γ(M, U))
    (x : V.analyticSpace) (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W) :
    f.onSection W (M.presheaf.map (homOfLE h).op z) ⟨x, hx⟩ = f.onSection U z ⟨x, h hx⟩ := by
  exact congrArg (fun a => a ⟨x, hx⟩) (f.section_restrict h z)

end HolomorphicScalarFunctional

def holomorphicScalarFunctionalOfAlgebraic {M : V.carrier.Modules}
    (f : M ⟶ HilbertConstruction.Line.Bundles.structureModule V.carrier) : HolomorphicScalarFunctional V M :=
  f ≫ SheafOfModules.unitToPushforwardObjUnit
    (F := Opens.map (DivisorClass.Chern.Holomorphic.RegularEvaluation.holomorphicAnalytificationPointMap V)) (DivisorClass.Chern.Holomorphic.RegularEvaluation.algebraicToHolomorphicStructureSheaf V)

theorem holomorphicScalarFunctionalOfAlgebraic_section {M : V.carrier.Modules}
    (f : M ⟶ HilbertConstruction.Line.Bundles.structureModule V.carrier) (U : V.carrier.Opens) (z : Γ(M, U)) :
    (holomorphicScalarFunctionalOfAlgebraic V f).onSection U z =
      DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V U (f.app U z) := rfl

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.FunctionalNe

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.FunctionalNe.HolomorphicScalarFunctional
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AnalytificationUnit
section

/-! Local coordinates of actual holomorphic scalar functionals use the
original algebraic frames and native regular-function evaluation. -/

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {M : V.carrier.Modules}
    (f : HolomorphicScalarFunctional V M)

theorem onSection_frame_expansion (r : LineFrameAtlas.LocalLineFrame M) (U : V.carrier.Opens)
    (hr : U ≤ r.domain) (z : Γ(M, U)) :
    f.onSection U z = DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V U (r.coordinates U hr z) *
      f.onSection U ((r.coordinates U hr).symm 1) := by
  exact (congrArg (f.onSection U) (LineFrameAtlas.rankOne_coordinate_expansion (r.coordinates U hr) z)).trans
    (f.section_smul U (r.coordinates U hr z) ((r.coordinates U hr).symm 1))

def localCoefficient (r : LineFrameAtlas.LocalLineFrame M) (s : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Line.Bundles.structureModule V.carrier))
    (U : V.carrier.Opens) (hr : U ≤ r.domain) (hs : U ≤ s.domain) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U) :=
  f.onSection U ((r.coordinates U hr).symm 1) *
    DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V U (s.coordinates U hs (1 : Γ(V.carrier, U)))

theorem localCoefficient_restrict (r : LineFrameAtlas.LocalLineFrame M)
    (s : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Line.Bundles.structureModule V.carrier)) {U W : V.carrier.Opens}
    (h : W ≤ U) (hr : U ≤ r.domain) (hs : U ≤ s.domain) :
    f.localCoefficient r s W (h.trans hr) (h.trans hs) =
      DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction (show DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W ≤
        DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U from fun _ hx => h hx)
          (f.localCoefficient r s U hr hs) := by
  have he : M.presheaf.map (homOfLE h).op ((r.coordinates U hr).symm 1) =
      (r.coordinates W (h.trans hr)).symm 1 := by
    apply (r.coordinates W (h.trans hr)).injective
    rw [r.coordinates_restrict h hr, LinearEquiv.apply_symm_apply, map_one, LinearEquiv.apply_symm_apply]
  have hg : s.coordinates W (h.trans hs) (1 : Γ(V.carrier, W)) =
      V.carrier.presheaf.map (homOfLE h).op (s.coordinates U hs (1 : Γ(V.carrier, U))) := by
    have hh := s.coordinates_restrict h hs (1 : Γ(V.carrier, U))
    change s.coordinates W (h.trans hs) (V.carrier.presheaf.map (homOfLE h).op (1 : Γ(V.carrier, U))) = _ at hh
    simpa only [map_one] using hh
  unfold HolomorphicScalarFunctional.localCoefficient
  rw [← he, f.section_restrict h, hg, DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation_restrict, map_mul]

theorem localCoefficient_frame_change (r₀ r₁ : LineFrameAtlas.LocalLineFrame M)
    (s₀ s₁ : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Line.Bundles.structureModule V.carrier)) (U : V.carrier.Opens)
    (hr₀ : U ≤ r₀.domain) (hr₁ : U ≤ r₁.domain) (hs₀ : U ≤ s₀.domain) (hs₁ : U ≤ s₁.domain) :
    DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V U (r₀.transition r₁ U hr₀ hr₁) *
      f.localCoefficient r₀ s₀ U hr₀ hs₀ =
    f.localCoefficient r₁ s₁ U hr₁ hs₁ *
      DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V U (s₀.transition s₁ U hs₀ hs₁) := by
  have he := f.onSection_frame_expansion r₀ U hr₀ ((r₁.coordinates U hr₁).symm 1)
  change f.onSection U ((r₁.coordinates U hr₁).symm 1) =
    DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V U (r₀.transition r₁ U hr₀ hr₁) *
      f.onSection U ((r₀.coordinates U hr₀).symm 1) at he
  have hg : s₀.coordinates U hs₀ (1 : Γ(V.carrier, U)) =
      (s₀.transition s₁ U hs₀ hs₁ : Γ(V.carrier, U)) * s₁.coordinates U hs₁ (1 : Γ(V.carrier, U)) := by
    exact (LineFrameAtlas.rankOneLinearMap_coefficient LinearMap.id (s₁.coordinates U hs₁)
      (s₀.coordinates U hs₀) (1 : Γ(V.carrier, U))).trans (mul_comm _ _)
  unfold HolomorphicScalarFunctional.localCoefficient
  rw [hg, map_mul, he]
  ring

end

section

/-! An actual holomorphic scalar functional supplies the compatible
native line-morphism coefficients required by algebraization. -/

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {L : HilbertConstruction.Line.Bundles.LineBundle V.carrier}
    (f : HolomorphicScalarFunctional V L.sheaf)

def coefficient (r : LineFrameAtlas.LocalLineFrame L.sheaf)
    (s : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Line.Bundles.structureModule V.carrier)) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel)
      (M := (AnalyticFrameTransitions.frameAnalyticOpen V.presentation r ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s : Opens V.analyticSpace)) :=
  f.localCoefficient r s (r.domain ⊓ s.domain) inf_le_left inf_le_right

theorem coefficient_value_on_open (r : LineFrameAtlas.LocalLineFrame L.sheaf)
    (s : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Line.Bundles.structureModule V.carrier)) (U : V.carrier.Opens)
    (hr : U ≤ r.domain) (hs : U ≤ s.domain) (x : V.analyticSpace)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ U) :
    f.coefficient r s ⟨x, hr hx, hs hx⟩ = f.localCoefficient r s U hr hs ⟨x, hx⟩ :=
  (congrArg (fun a => a ⟨x, hx⟩)
    (f.localCoefficient_restrict r s (le_inf hr hs) inf_le_left inf_le_right)).symm

theorem coefficient_frame_change (r₀ r₁ : LineFrameAtlas.LocalLineFrame L.sheaf)
    (s₀ s₁ : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Line.Bundles.structureModule V.carrier)) (x : V.analyticSpace)
    (h₀ : x ∈ AnalyticFrameTransitions.frameAnalyticOpen V.presentation r₀ ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s₀)
    (h₁ : x ∈ AnalyticFrameTransitions.frameAnalyticOpen V.presentation r₁ ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s₁) :
    AnalyticFrameTransitions.framePointTransition V.presentation r₀ r₁ x h₀.1 h₁.1 * f.coefficient r₀ s₀ ⟨x, h₀⟩ =
      f.coefficient r₁ s₁ ⟨x, h₁⟩ * AnalyticFrameTransitions.framePointTransition V.presentation s₀ s₁ x h₀.2 h₁.2 := by
  let W := (r₀.domain ⊓ s₀.domain) ⊓ (r₁.domain ⊓ s₁.domain)
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W := ⟨h₀, h₁⟩
  have hr₀ : W ≤ r₀.domain := inf_le_left.trans inf_le_left
  have hr₁ : W ≤ r₁.domain := inf_le_right.trans inf_le_left
  have hs₀ : W ≤ s₀.domain := inf_le_left.trans inf_le_right
  have hs₁ : W ≤ s₁.domain := inf_le_right.trans inf_le_right
  have hr := AnalyticFrameTransitions.framePointTransition_restrict V.presentation r₀ r₁ W hr₀ hr₁ ⟨x, hx⟩
  have hs := AnalyticFrameTransitions.framePointTransition_restrict V.presentation s₀ s₁ W hs₀ hs₁ ⟨x, hx⟩
  have he := congrArg (fun a : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel)
    (M := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) => a ⟨x, hx⟩)
      (f.localCoefficient_frame_change r₀ r₁ s₀ s₁ W hr₀ hr₁ hs₀ hs₁)
  change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation W (r₀.transition r₁ W hr₀ hr₁) ⟨x, hx⟩ *
      f.localCoefficient r₀ s₀ W hr₀ hs₀ ⟨x, hx⟩ =
    f.localCoefficient r₁ s₁ W hr₁ hs₁ ⟨x, hx⟩ *
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation W (s₀.transition s₁ W hs₀ hs₁) ⟨x, hx⟩ at he
  rw [← hr, ← hs, ← f.coefficient_value_on_open r₀ s₀ W hr₀ hs₀ x hx,
    ← f.coefficient_value_on_open r₁ s₁ W hr₁ hs₁ x hx] at he
  exact he

def coefficients : LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V L (HilbertConstruction.Line.Bundles.LineBundle.trivial V.carrier) where
  coefficient := f.coefficient
  frame_change := f.coefficient_frame_change

theorem coefficients_of_algebraic (g : L.sheaf ⟶ HilbertConstruction.Line.Bundles.structureModule V.carrier) :
    (holomorphicScalarFunctionalOfAlgebraic V g).coefficients =
      LineMorphismCoefficients.holomorphicLineMorphismCoefficientsOfAlgebraic V L (HilbertConstruction.Line.Bundles.LineBundle.trivial V.carrier) g := by
  apply LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.ext
  intro r s
  let U := r.domain ⊓ s.domain
  have h := LineFrameAtlas.rankOneLinearMap_coefficient LinearMap.id (LinearEquiv.refl Γ(V.carrier, U) Γ(V.carrier, U))
    (s.coordinates U inf_le_right) (g.app U ((r.coordinates U inf_le_left).symm 1))
  change s.coordinates U inf_le_right (g.app U ((r.coordinates U inf_le_left).symm 1)) =
    (show Γ(V.carrier, U) from g.app U ((r.coordinates U inf_le_left).symm 1)) *
      s.coordinates U inf_le_right (1 : Γ(V.carrier, U)) at h
  change DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V U (g.app U ((r.coordinates U inf_le_left).symm 1)) *
      DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V U (s.coordinates U inf_le_right (1 : Γ(V.carrier, U))) =
    DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V U (s.coordinates U inf_le_right
      (g.app U ((r.coordinates U inf_le_left).symm 1)))
  rw [h, map_mul]

end

/-! Literal frame coefficients detect actual maps into the direct image
of the native holomorphic structure module. -/

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {L : HilbertConstruction.Line.Bundles.LineBundle V.carrier}

theorem structureFrame_coordinate_one_ne_zero
    (s : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Line.Bundles.structureModule V.carrier)) (U : V.carrier.Opens)
    (hs : U ≤ s.domain) (x : V.analyticSpace) (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ U) :
    DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V U (s.coordinates U hs (1 : Γ(V.carrier, U))) ⟨x, hx⟩ ≠ 0 := by
  let u : Γ(V.carrier, U)ˣ := DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit (s.coordinates U hs)
    (LinearEquiv.refl Γ(V.carrier, U) Γ(V.carrier, U))
  have hu : (u : Γ(V.carrier, U)) = s.coordinates U hs (1 : Γ(V.carrier, U)) := rfl
  have h := (u.isUnit.map (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left U hx)).ne_zero
  rw [hu] at h
  exact (Intrinsic.FrameEvaluation.sectionEvaluationOn_native V.presentation U _ ⟨x, hx⟩).trans_ne h

theorem coefficients_injective :
    Function.Injective (fun f : HolomorphicScalarFunctional V L.sheaf => f.coefficients) := by
  intro f g he
  apply Scheme.Modules.hom_ext
  intro U
  ext z
  change f.onSection U z = g.onSection U z
  apply DFunLike.ext
  intro x
  obtain ⟨r, hr⟩ := LineFrameAtlas.localLineFrames_cover L (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val)
  obtain ⟨s, hs⟩ := LineFrameAtlas.localLineFrames_cover (HilbertConstruction.Line.Bundles.LineBundle.trivial V.carrier)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val)
  let W := U ⊓ (r.domain ⊓ s.domain)
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ W := ⟨x.property, hr, hs⟩
  have hWU : W ≤ U := inf_le_left
  have hWr : W ≤ r.domain := inf_le_right.trans inf_le_left
  have hWs : W ≤ s.domain := inf_le_right.trans inf_le_right
  have hc := congrArg (fun D : LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V L (HilbertConstruction.Line.Bundles.LineBundle.trivial V.carrier) =>
    D.coefficient r s ⟨x.val, hr, hs⟩) he
  change f.coefficient r s ⟨x.val, hr, hs⟩ = g.coefficient r s ⟨x.val, hr, hs⟩ at hc
  rw [f.coefficient_value_on_open r s W hWr hWs x.val hx,
    g.coefficient_value_on_open r s W hWr hWs x.val hx] at hc
  change f.onSection W ((r.coordinates W hWr).symm 1) ⟨x.val, hx⟩ *
      DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V W (s.coordinates W hWs (1 : Γ(V.carrier, W))) ⟨x.val, hx⟩ =
    g.onSection W ((r.coordinates W hWr).symm 1) ⟨x.val, hx⟩ *
      DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V W (s.coordinates W hWs (1 : Γ(V.carrier, W))) ⟨x.val, hx⟩ at hc
  have hg := mul_right_cancel₀ (structureFrame_coordinate_one_ne_zero s W hWs x.val hx) hc
  let w := L.sheaf.presheaf.map (homOfLE hWU).op z
  have hf₀ := congrArg (fun a => a ⟨x.val, hx⟩) (f.onSection_frame_expansion r W hWr w)
  have hg₀ := congrArg (fun a => a ⟨x.val, hx⟩) (g.onSection_frame_expansion r W hWr w)
  change f.onSection W w ⟨x.val, hx⟩ =
    DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V W (r.coordinates W hWr w) ⟨x.val, hx⟩ *
      f.onSection W ((r.coordinates W hWr).symm 1) ⟨x.val, hx⟩ at hf₀
  change g.onSection W w ⟨x.val, hx⟩ =
    DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V W (r.coordinates W hWr w) ⟨x.val, hx⟩ *
      g.onSection W ((r.coordinates W hWr).symm 1) ⟨x.val, hx⟩ at hg₀
  exact (f.section_value_restrict hWU z x.val hx).symm.trans
    (hf₀.trans ((congrArg (DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V W (r.coordinates W hWr w) ⟨x.val, hx⟩ * ·) hg).trans
      (hg₀.symm.trans (g.section_value_restrict hWU z x.val hx))))

theorem exists_algebraic (f : HolomorphicScalarFunctional V L.sheaf) :
    ∃ g : L.sheaf ⟶ HilbertConstruction.Line.Bundles.structureModule V.carrier, holomorphicScalarFunctionalOfAlgebraic V g = f := by
  obtain ⟨g, hg⟩ := f.coefficients.exists_algebraic
  exact ⟨g, coefficients_injective ((coefficients_of_algebraic g).trans hg)⟩

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.FunctionalNe.HolomorphicScalarFunctional

end

end OAI
