import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionGenerators

/-! # Local Freeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalFreeness

noncomputable section

/-! On any open contained in one frame chart, compatible frame-coordinate sections form a free module of rank one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}

theorem openFunctionRestriction_bijective_of_eq {V W : X.Opens} (h : W ≤ V) (he : W = V) :
    Function.Bijective (X.presheaf.map (homOfLE h).op) := by
  have : IsIso (homOfLE h) := homOfLE_isIso_of_eq h he
  exact ConcreteCategory.bijective_of_isIso (X.presheaf.map (homOfLE h).op)

variable (D : Transitions.OpenFrameTransitions U)

theorem openFrameGenerator_injective (V : X.Opens) (k : ι) (hV : V ≤ U k) :
    Function.Injective (SectionGenerators.openFrameGenerator D V k hV) := by
  intro x y h
  apply (openFunctionRestriction_bijective_of_eq inf_le_left (inf_eq_left.mpr hV)).injective
  exact (D.frameValues_self V k hV x).symm.trans
    ((congrArg (fun s : SectionModules.openFrameSectionModule U D V => s.val k) h).trans (D.frameValues_self V k hV y))

theorem openFrameGenerator_surjective (V : X.Opens) (k : ι) (hV : V ≤ U k) :
    Function.Surjective (SectionGenerators.openFrameGenerator D V k hV) := by
  intro s
  obtain ⟨x, hx⟩ := (openFunctionRestriction_bijective_of_eq inf_le_left (inf_eq_left.mpr hV)).surjective (s.val k)
  refine ⟨x, Subtype.ext ?_⟩
  funext i
  let W := (V ⊓ U i) ⊓ U k
  have hWi : W ≤ V ⊓ U i := inf_le_left
  have hWk : W ≤ V ⊓ U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have heW : W = V ⊓ U i := inf_eq_left.mpr (inf_le_left.trans hV)
  apply (openFunctionRestriction_bijective_of_eq hWi heW).injective
  have hs := (SectionModules.openFrameSectionModule_mem_iff U D V s.val).mp s.property i k
  have hx' := congrArg (fun z : Γ(X, V ⊓ U k) => X.presheaf.map (homOfLE hWk).op z) hx
  have hk : X.presheaf.map (homOfLE hWk).op (s.val k) =
      X.presheaf.map (homOfLE (hWi.trans inf_le_left)).op x :=
    hx'.symm.trans (Relative.OpenFunctionUnits.openFunction_restriction_comp inf_le_left hWk x)
  exact (D.frameValues_restrict V k hV x i W hWi).trans
    ((congrArg (fun z : Γ(X, W) =>
      (D.value W i k (hWi.trans inf_le_right) (hWi.trans (inf_le_left.trans hV))).val * z) hk).symm.trans hs.symm)

def openFrameLocalEquiv (V : X.Opens) (k : ι) (hV : V ≤ U k) :
    Γ(X, V) ≃ₗ[Γ(X, V)] SectionModules.openFrameSectionModule U D V :=
  LinearEquiv.ofBijective (SectionGenerators.openFrameGenerator D V k hV)
    ⟨openFrameGenerator_injective D V k hV, openFrameGenerator_surjective D V k hV⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalFreeness
