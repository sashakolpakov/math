import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FunctionGluing

/-! # Cocycle Pullback -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.CocyclePullback

noncomputable section

section

/-! Pulling back native regular functions along an actual scheme morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme} (f : X ⟶ Y)

def regularPullback {V : Y.Opens} {U : X.Opens} (hUV : U ≤ f ⁻¹ᵁ V) : Γ(Y, V) →+* Γ(X, U) :=
  (f.appLE V U hUV).hom

theorem regularPullback_res {V : Y.Opens} {U W : X.Opens}
    (hUV : U ≤ f ⁻¹ᵁ V) (hWU : W ≤ U) (s : Γ(Y, V)) :
    FunctionGluing.regularRestriction hWU (regularPullback f hUV s) =
      regularPullback f (hWU.trans hUV) s :=
  ConcreteCategory.congr_hom (f.appLE_map hUV (homOfLE hWU).op) s

theorem regularPullback_restrict {V T : Y.Opens} {U : X.Opens}
    (hUV : U ≤ f ⁻¹ᵁ V) (hVT : V ≤ T) (s : Γ(Y, T)) :
    regularPullback f hUV (FunctionGluing.regularRestriction hVT s) =
      regularPullback f (hUV.trans ((Opens.map f.base).map (homOfLE hVT)).le) s :=
  ConcreteCategory.congr_hom (f.map_appLE hUV (homOfLE hVT).op) s

end

/-! Native pullback of actual regular unit cocycles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme} {ι : Type} (D : FunctionGluing.RegularLineCocycle Y ι) (f : X ⟶ Y)

def pullbackRegularTransition (i j : ι) (W : X.Opens)
    (hi : W ≤ f ⁻¹ᵁ D.domain i) (hj : W ≤ f ⁻¹ᵁ D.domain j) : Γ(X, W)ˣ :=
  Units.map (regularPullback f (show W ≤ f ⁻¹ᵁ (D.domain i ⊓ D.domain j) from le_inf hi hj)).toMonoidHom
    (D.transition i j (D.domain i ⊓ D.domain j) inf_le_left inf_le_right)

theorem pullbackRegularTransition_on_subopen (i j : ι) (W : X.Opens) (V : Y.Opens)
    (hWV : W ≤ f ⁻¹ᵁ V) (hi : V ≤ D.domain i) (hj : V ≤ D.domain j) :
    (pullbackRegularTransition D f i j W
      (hWV.trans ((Opens.map f.base).map (homOfLE hi)).le)
      (hWV.trans ((Opens.map f.base).map (homOfLE hj)).le) : Γ(X, W)) =
      regularPullback f hWV (D.transition i j V hi hj : Γ(Y, V)) := by
  change regularPullback f
    (show W ≤ f ⁻¹ᵁ (D.domain i ⊓ D.domain j) from
      le_inf (hWV.trans ((Opens.map f.base).map (homOfLE hi)).le)
        (hWV.trans ((Opens.map f.base).map (homOfLE hj)).le))
    (D.transition i j (D.domain i ⊓ D.domain j) inf_le_left inf_le_right :
      Γ(Y, D.domain i ⊓ D.domain j)) = _
  rw [← D.restrict i j (D.domain i ⊓ D.domain j) V (le_inf hi hj) inf_le_left inf_le_right,
    regularPullback_restrict]

def regularCocyclePullback : FunctionGluing.RegularLineCocycle X ι where
  domain i := f ⁻¹ᵁ D.domain i
  covers := by
    apply top_unique
    intro x _
    have hx : f x ∈ iSup D.domain := by rw [D.covers]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  transition := pullbackRegularTransition D f
  restrict i j U W hWU hi hj := by
    exact regularPullback_res f (show U ≤ f ⁻¹ᵁ (D.domain i ⊓ D.domain j) from le_inf hi hj)
      hWU (D.transition i j (D.domain i ⊓ D.domain j) inf_le_left inf_le_right)
  refl i W hi := by
    apply Units.ext
    rw [pullbackRegularTransition_on_subopen D f i i W (D.domain i) hi le_rfl le_rfl,
      D.refl, Units.val_one, map_one]
    rfl
  cocycle i j k W hi hj hk := by
    apply Units.ext
    let V := D.domain i ⊓ D.domain j ⊓ D.domain k
    have hWV : W ≤ f ⁻¹ᵁ V := le_inf (le_inf hi hj) hk
    have hVi : V ≤ D.domain i := inf_le_left.trans inf_le_left
    have hVj : V ≤ D.domain j := inf_le_left.trans inf_le_right
    have hVk : V ≤ D.domain k := inf_le_right
    change (pullbackRegularTransition D f i j W hi hj : Γ(X, W)) *
        (pullbackRegularTransition D f j k W hj hk : Γ(X, W)) =
      (pullbackRegularTransition D f i k W hi hk : Γ(X, W))
    rw [pullbackRegularTransition_on_subopen D f i j W V hWV hVi hVj,
      pullbackRegularTransition_on_subopen D f j k W V hWV hVj hVk,
      pullbackRegularTransition_on_subopen D f i k W V hWV hVi hVk, ← map_mul]
    exact congrArg (regularPullback f hWV) (congrArg (fun t : Γ(Y, V)ˣ => (t : Γ(Y, V)))
      (D.cocycle i j k V hVi hVj hVk))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.CocyclePullback
