import OAI.AlgebraicGeometry.Comparison.Betti.GermCoordinateEquiv
import OAI.AlgebraicGeometry.Comparison.Betti.RegularHolomorphicLine
import OAI.AlgebraicGeometry.Comparison.Betti.LinearCoordinateDirection
import OAI.AlgebraicGeometry.Comparison.Betti.GermPreparation

/-! # Germ Regularization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.GermRegularization.AnalyticLocal

noncomputable section

/-! An explicit affine coordinate change makes any nonzero holomorphic
germ vertically regular. -/

open Set Filter
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def affineCoordinateEquiv (p : E) (L : E ≃L[ℂ] E) : E ≃ E where
  toFun q := p + L q
  invFun q := L.symm (q - p)
  left_inv q := by simp
  right_inv q := by simp

theorem affineCoordinateEquiv_differentiable (p : E) (L : E ≃L[ℂ] E) :
    Differentiable ℂ (affineCoordinateEquiv p L) :=
  (differentiable_const p).add L.differentiable

theorem affineCoordinateEquiv_symm_differentiable (p : E) (L : E ≃L[ℂ] E) :
    Differentiable ℂ (affineCoordinateEquiv p L).symm :=
  L.symm.differentiable.comp (differentiable_id.sub (differentiable_const p))

theorem exists_regular_germ_coordinate_equiv [FiniteDimensional ℂ E]
    (x : E) (c : ℂ) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c)) (ha : a ≠ 0) :
    ∃ e : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c) ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (0 : E × ℂ),
      GermPreparation.AnalyticLocal.verticalRestriction (0 : E) 0 (e a) ≠ 0 := by
  obtain ⟨F, hFa, W, hW, hp, hF⟩ := a.property
  have hn : ¬∀ᶠ p in 𝓝 (x, c), F p = 0 := by
    intro hz
    apply ha
    apply Subtype.ext
    rw [← hFa]
    exact Germ.coe_eq.mpr hz
  obtain ⟨v, hv, hline⟩ := RegularHolomorphicLine.AnalyticLocal.exists_regular_holomorphic_line hW hF hp hn
  have haxis : ((0, 1) : E × ℂ) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Prod.snd h)
  obtain ⟨L, hL⟩ := LinearCoordinateDirection.AnalyticLocal.exists_coordinate_linear_equiv ((0, 1) : E × ℂ) v haxis hv
  let e := affineCoordinateEquiv (x, c) L
  have he := affineCoordinateEquiv_differentiable (x, c) L
  have hi := affineCoordinateEquiv_symm_differentiable (x, c) L
  have he0 : e 0 = (x, c) := by simp [e, affineCoordinateEquiv]
  let ψ := (GermCoordinateEquiv.AnalyticLocal.holomorphicGermEquivAt e he hi 0 (x, c) he0).symm
  have heline : ∀ z : ℂ, e (0, z) = (x, c) + z • v := by
    intro z
    change (x, c) + L (0, z) = _
    congr 1
    calc
      L (0, z) = L (z • ((0, 1) : E × ℂ)) := by congr 1; simp
      _ = z • L (0, 1) := L.map_smul z (0, 1)
      _ = z • v := by rw [hL]
  have hψ : (ψ a).val = ((F ∘ e) : Germ (𝓝 (0 : E × ℂ)) ℂ) := by
    change ((GermCoordinateEquiv.AnalyticLocal.holomorphicGermEquivAt e he hi 0 (x, c) he0).symm a).val = _
    rw [GermCoordinateEquiv.AnalyticLocal.holomorphicGermEquivAt_symm_val, ← hFa]
    rfl
  refine ⟨ψ, ?_⟩
  intro hz
  have hzero := congrArg Subtype.val hz
  change GermComposition.AnalyticLocal.germComposition (fun z : ℂ => ((0 : E), z)) _ (ψ a).val = 0 at hzero
  rw [hψ] at hzero
  have hzero' : ∀ᶠ z in 𝓝 (0 : ℂ), F (e (0, z)) = 0 := Germ.coe_eq.mp hzero
  apply hline
  filter_upwards [hzero'] with z hz
  simpa only [heline z] using hz

end

end OAI.AlgebraicGeometry.Comparison.Betti.GermRegularization.AnalyticLocal
