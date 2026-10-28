import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Instances.Int

/-! # Moving Lattice Action -/

namespace OAI.RepresentationTheory.Theta.Geometric.MovingLatticeAction

noncomputable section

section

/-! A continuous endomorphism preserving a continuously framed full
integral lattice has constant integer coordinates near each parameter. -/

set_option backward.isDefEq.respectTransparency false
open scoped _root_.Topology

variable {S V : Type} [TopologicalSpace S]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (Λ : S → Submodule ℤ V)
    (b : ∀ s, Module.Basis (Fin n) ℤ (Λ s))
    (r : S → (Fin n → ℝ) ≃L[ℝ] V)
    (hb : ∀ s i, (b s i : V) = r s (Pi.single i 1))

include hb

omit [TopologicalSpace S] in
theorem movingLattice_coordinates (s : S) (v : Λ s) (i : Fin n) :
    (r s).symm (v : V) i = ((b s).repr v i : ℝ) := by
  classical
  have h := congrArg (fun w : Λ s => (w : V)) ((b s).sum_repr v)
  have hr (j : Fin n) : (r s).symm (b s j : V) = Pi.single j 1 := by
    rw [hb, ContinuousLinearEquiv.symm_apply_apply]
  rw [← h]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, map_sum, map_zsmul, hr,
    Finset.sum_apply, zsmul_eq_mul]
  simp [Pi.single_apply]

theorem movingLatticeAction_locally_constant
    (D : S → V →L[ℝ] V) (hDΛ : ∀ s v, v ∈ Λ s → D s v ∈ Λ s)
    (s₀ : S)
    (hr : ContinuousAt (fun s => (r s).toContinuousLinearMap) s₀)
    (hD : ContinuousAt D s₀) :
    ∀ᶠ s in 𝓝 s₀, ∀ v : Fin n → ℝ,
      (r s).symm (D s (r s v)) = (r s₀).symm (D s₀ (r s₀ v)) := by
  classical
  let entry := fun s (i j : Fin n) =>
    (b s).repr ⟨D s (b s j : V), hDΛ s _ (b s j).property⟩ i
  have he (s : S) (i j : Fin n) :
      (r s).symm (D s (r s (Pi.single j 1))) i = (entry s i j : ℝ) := by
    rw [← hb s j]
    exact movingLattice_coordinates Λ b r hb s
      ⟨D s (b s j : V), hDΛ s _ (b s j).property⟩ i
  have hconstant (i j : Fin n) : ∀ᶠ s in 𝓝 s₀, entry s i j = entry s₀ i j := by
    have hi : ContinuousAt
        (ContinuousLinearMap.inverse : ((Fin n → ℝ) →L[ℝ] V) → (V →L[ℝ] (Fin n → ℝ)))
        (r s₀).toContinuousLinearMap :=
      (contDiffAt_map_inverse (n := 0) (r s₀)).continuousAt
    have hinv := ContinuousAt.comp (f := fun s => (r s).toContinuousLinearMap)
      (x := s₀) hi hr
    have hv := hD.clm_apply (hr.clm_apply (continuousAt_const (y := Pi.single j 1)))
    have hc := (continuous_apply i).continuousAt.comp (hinv.clm_apply hv)
    have hreal : ContinuousAt (fun s => (entry s i j : ℝ)) s₀ := by
      simpa only [Function.comp_def, ContinuousLinearMap.inverse_equiv,
        ContinuousLinearEquiv.coe_coe, he] using hc
    have hz : ContinuousAt (fun s => entry s i j) s₀ :=
      Int.isClosedEmbedding_coe_real.isEmbedding.isInducing.continuousAt_iff.mpr hreal
    exact hz.eventually ((isOpen_discrete {entry s₀ i j}).mem_nhds rfl)
  have hall : ∀ᶠ s in 𝓝 s₀, ∀ i j, entry s i j = entry s₀ i j := by
    simpa only [Filter.eventually_all] using hconstant
  filter_upwards [hall] with s hs
  have hm : ((r s).symm.toLinearMap.comp ((D s).toLinearMap.comp (r s).toLinearMap)) =
      ((r s₀).symm.toLinearMap.comp ((D s₀).toLinearMap.comp (r s₀).toLinearMap)) := by
    apply (Pi.basisFun ℝ (Fin n)).ext
    intro j
    funext i
    simp only [Pi.basisFun_apply]
    change (r s).symm (D s (r s (Pi.single j 1))) i =
      (r s₀).symm (D s₀ (r s₀ (Pi.single j 1))) i
    rw [he, he, hs]
  exact fun v => LinearMap.congr_fun hm v

end

/-! The literal real change of a full integral frame preserves its
lattices in both directions. -/

set_option backward.isDefEq.respectTransparency false

variable {S V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (Λ : S → Submodule ℤ V) (b : ∀ s, Module.Basis (Fin n) ℤ (Λ s))
    (r : S → (Fin n → ℝ) ≃L[ℝ] V)
    (hb : ∀ s i, (b s i : V) = r s (Pi.single i 1))

include hb

theorem movingLattice_transport (s t : S) (v : V) (hv : v ∈ Λ s) :
    r t ((r s).symm v) ∈ Λ t := by
  let u : Λ s := ⟨v, hv⟩
  let w : Λ t := (b t).repr.symm ((b s).repr u)
  have hw : (r t).symm (w : V) = (r s).symm v := by
    funext i
    rw [movingLattice_coordinates Λ b r hb t w i,
      movingLattice_coordinates Λ b r hb s u i]
    exact congrArg (fun z : ℤ => (z : ℝ))
      (congrArg (fun z => z i) ((b t).repr.apply_symm_apply ((b s).repr u)))
  rw [← hw, ContinuousLinearEquiv.apply_symm_apply]
  exact w.property

theorem movingLattice_transport_iff (s t : S) (v : V) :
    r t ((r s).symm v) ∈ Λ t ↔ v ∈ Λ s := by
  constructor
  · intro hv
    have h := movingLattice_transport Λ b r hb t s _ hv
    simpa only [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply] using h
  · exact movingLattice_transport Λ b r hb s t v

end

end OAI.RepresentationTheory.Theta.Geometric.MovingLatticeAction
