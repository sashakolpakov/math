import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalCoefficient
import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.PullbackSquareSections

/-! # Pullback Generic Independence -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackGenericIndependence.Cycles

noncomputable section

/-! # LineBundleCycles: arbitrary actual pullbacks agree wherever two regular sections represent the same generic section -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

theorem lineBundlePullback_genericCoefficient_eq (U V : X.Opens) [Nonempty U] [Nonempty V]
    [Nonempty (f ⁻¹ᵁ U)] [Nonempty (f ⁻¹ᵁ V)]
    (s : Γ(L.sheaf, U)) (t : Γ(L.sheaf, V))
    (h : L.genericSectionCoefficient U s = L.genericSectionCoefficient V t) :
    (L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ U) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s) =
      (L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ V) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf V t) := by
  let W : X.Opens := U ⊓ V
  let : Nonempty W := ⟨⟨genericPoint X,
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›),
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)⟩⟩
  let S := f ⁻¹ᵁ W
  let : Nonempty S := ⟨⟨genericPoint Y,
    ((genericPoint_spec Y).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).mpr (by simpa using ‹Nonempty (f ⁻¹ᵁ U)›),
    ((genericPoint_spec Y).mem_open_set_iff (f ⁻¹ᵁ V).isOpen).mpr (by simpa using ‹Nonempty (f ⁻¹ᵁ V)›)⟩⟩
  have hWU : W ≤ U := inf_le_left
  have hWV : W ≤ V := inf_le_right
  have hs : L.sheaf.presheaf.map (homOfLE hWU).op s = L.sheaf.presheaf.map (homOfLE hWV).op t := by
    apply L.genericSectionCoefficient_injective W
    rw [L.genericSectionCoefficient_restrict hWU, L.genericSectionCoefficient_restrict hWV]
    exact h
  have hP := (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen_restrict f L.sheaf hWU s).trans
    ((congrArg (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf W) hs).trans
      (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen_restrict f L.sheaf hWV t).symm)
  have hSU : S ≤ f ⁻¹ᵁ U := fun _ h => h.1
  have hSV : S ≤ f ⁻¹ᵁ V := fun _ h => h.2
  calc
    _ = (L.pullback f).genericSectionCoefficient S
        ((L.pullback f).sheaf.presheaf.map (homOfLE hSU).op (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s)) :=
      ((L.pullback f).genericSectionCoefficient_restrict hSU _).symm
    _ = (L.pullback f).genericSectionCoefficient S
        ((L.pullback f).sheaf.presheaf.map (homOfLE hSV).op (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf V t)) :=
      congrArg ((L.pullback f).genericSectionCoefficient S) hP
    _ = _ := (L.pullback f).genericSectionCoefficient_restrict hSV _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackGenericIndependence.Cycles
