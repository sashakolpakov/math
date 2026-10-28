import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelFiberNonzero
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionValue
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TrivialBundle
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionTriviality

/-! # Model Frame -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelFrame

noncomputable section

/-! A global model cycle surviving on a trivial proper fiber gives a
trivialization on a neighborhood of that fiber. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.ModelFrameNeighborhood

variable {X S : Scheme.{u}} (π : X ⟶ S) [IsProper π] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π L.sheaf U) [QuasiIsoAt φ 0]

include φ hU

theorem exists_open (x : S) [ConnectedSpace (π.fiber x)] [IsReduced (π.fiber x)]
    (he : Nonempty ((L.pullback (π.fiberι x)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber x)))
    (hφ : QuasiIsoAt (CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (π.fiberι x) π
      (π.fiberToSpecResidueField x) (S.fromSpecResidueField x) (π.fiber_fac x) L.sheaf U φ) 0)
    (z : (D.d 0 1).hom.ker)
    (hz : (ModelOneTensor.Construction.CechBaseChangeMap.oneCycle (S.fromSpecResidueField x) z).val ≠ 0) :
    ∃ V : S.Opens, x ∈ V ∧
      Nonempty ((L.pullback (π ⁻¹ᵁ V).ι).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π ⁻¹ᵁ V).toScheme) := by
  have := hφ
  let a := GlobalModel.Construction.GlobalModelSections.equiv π L.sheaf U hU φ z
  let s := (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm a
  have hs : AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (π.fiberι x) s ≠ 0 := by
    intro h
    have ha := PullbackSectionValue.Construction.PullbackSectionZero.value_zero (π.fiberι x) s h
    have hv : AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf s = a := (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).apply_symm_apply a
    rw [hv] at ha
    exact ModelFiberNonzero.Construction.CechBaseChangeMap.global_section_pullback_ne_zero (π.fiberι x) π
      (π.fiberToSpecResidueField x) (S.fromSpecResidueField x) (π.fiber_fac x)
      L.sheaf U hU φ z hz ha
  let F := Over.mk (π.fiberToSpecResidueField x)
  have : IsProper F.hom := inferInstanceAs (IsProper (pullback.snd π (S.fromSpecResidueField x)))
  have : ConnectedSpace F.left := inferInstanceAs (ConnectedSpace (π.fiber x))
  have : IsReduced F.left := inferInstanceAs (IsReduced (π.fiber x))
  have hi := TrivialBundle.Construction.TrivialBundleFrame.isIso F he.some (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (π.fiberι x) s) hs
  obtain ⟨V, hx, hV⟩ := SectionTriviality.Construction.SectionTrivialityOpen.exists_open π L s x hi
  exact ⟨V, hx, ⟨(asIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (π ⁻¹ᵁ V).ι s)).symm⟩⟩

end Construction.ModelFrameNeighborhood

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelFrame
