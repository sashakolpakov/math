import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.LogarithmicFiniteFamily
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.LogarithmicProgramNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.AuxiliaryPrefixBoundary
import Mathlib.Logic.Equiv.Option

/-! # Auxiliary Program -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface.AuxiliaryProgram.Construction

noncomputable section

/-! Surface auxiliary programs retain the full labelled boundary while using a common logarithmic coefficient program. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def SurfaceAuxiliaryProgram (n ℓ : ℕ) (β : Type) [Fintype β] [DecidableEq β]
    (X : Scheme) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (J : X.IdealSheafData) (D : β → X.IdealSheafData) (j : β)
    (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K) : Prop :=
  LogarithmicProgram.Construction.SurfaceLogarithmicProgram n ℓ {l : β // l ≠ j} X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1))
    (fun l => D l.val) Y g K P

namespace SurfaceAuxiliaryProgram

theorem uniformBoundaryCompatible
    {n ℓ : ℕ} {β : Type} [Fintype β] [DecidableEq β] {X Y : Scheme}
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData} {j : β}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K}
    (T : SurfaceAuxiliaryProgram n ℓ β X f J D j Y g K P)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) : P.uniformBoundaryCompatible β D := by
  classical
  let γ := {l : β // l ≠ j}
  let E : γ → X.IdealSheafData := fun l => D l.val
  have hT : P.uniformBoundaryCompatible γ E := LogarithmicProgram.Construction.SurfaceLogarithmicProgram.uniformBoundaryCompatible T
  let e : Option γ ≃ β := Equiv.optionSubtypeNe j
  let F : Option γ → X.IdealSheafData := fun l => match l with | none => D j | some s => E s
  have hF (l : Option γ) : F l = D (e l) := by cases l <;> rfl
  let AF : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f F [Finset.univ] :=
    A.pullbackLabels (fun l => some (e l))
      (fun l l' s hl hl' => e.injective (Option.some_injective _ (hl.trans hl'.symm))) F hF
  have hPF : P.uniformBoundaryCompatible (Option γ) F :=
    P.uniformBoundaryCompatible_adjoin_auxiliary_carrier (Nat.succ_pos n) J (D j) rfl γ E hT
      (by convert AF using 1)
  have ht := P.uniformBoundaryCompatible_reindex (Option γ) β F hPF e.symm.toEmbedding
  change P.uniformBoundaryCompatible β (fun l => F (e.symm l)) at ht
  have heq : (fun l => F (e.symm l)) = D := by
    funext l
    exact (hF (e.symm l)).trans (congrArg D (e.apply_symm_apply l))
  rwa [heq] at ht

theorem terminal_order
    {n ℓ : ℕ} {β : Type} [Fintype β] [DecidableEq β] {X Y : Scheme}
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData} {j : β}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K}
    (T : SurfaceAuxiliaryProgram n ℓ β X f J D j Y g K P) :
    letI : Smooth g := P.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤ := LogarithmicProgram.Construction.SurfaceLogarithmicProgram.terminal_order T

theorem exists_etaleComparison
    {n ℓ : ℕ} {β : Type} [Fintype β] [DecidableEq β] {X Y V W : Scheme}
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    {D : β → X.IdealSheafData} {E : β → V.IdealSheafData} {j : β}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K}
    {Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V h (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal L (E j) (n + 1)) W k M}
    (T : SurfaceAuxiliaryProgram n ℓ β X f J D j Y g K P)
    (S : SurfaceAuxiliaryProgram n ℓ β V h L E j W k M Q)
    (q : V ⟶ X) [Etale q] (hstructure : q ≫ f = h) (hJ : J.comap q = L)
    (hD : ∀ l, (D l).comap q = E l) : ∃ r : W ⟶ Y, P.EtaleComparison Q q r := by
  apply LogarithmicProgram.Construction.SurfaceLogarithmicProgram.exists_etaleComparison T S q hstructure
  · rw [GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_comap, hJ, hD]
  · intro l
    exact hD l.val

end SurfaceAuxiliaryProgram

theorem exists_surface_auxiliary_program_threshold
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (n : ℕ)
    (hd : topologicalKrullDim X ≤ 2) {β : Type} [Fintype β] [DecidableEq β]
    (D : β → X.IdealSheafData) (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) (j : β) :
    ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ →
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K),
        SurfaceAuxiliaryProgram n ℓ β X f J D j Y g K P := by
  classical
  obtain ⟨B⟩ := A.exists_modelAtlas
  let γ := {l : β // l ≠ j}
  let e : γ ↪ β := ⟨Subtype.val, Subtype.val_injective⟩
  let E : γ → X.IdealSheafData := fun l => D (e l)
  let AE : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f E [Finset.univ] :=
    A.pullbackLabels (fun l => some (e l))
      (fun a b s ha hb => e.injective (Option.some_injective _ (ha.trans hb.symm))) E (fun _ => rfl)
  have hlog : (B.reindex e).logarithmicIdeal (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) (n + 1) = ⊤ :=
    B.old_boundary_auxiliary_logarithmic_bound j e (fun l h => l.property h.symm) J (D j) le_rfl (n + 1)
  exact LogarithmicFiniteFamily.Construction.exists_surface_logarithmic_program_threshold f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) n hd
    E AE (B.reindex e) hlog

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface.AuxiliaryProgram.Construction
