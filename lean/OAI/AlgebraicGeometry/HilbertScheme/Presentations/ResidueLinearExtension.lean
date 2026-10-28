import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Residue Linear Extension -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ResidueLinearExtension

noncomputable section

/-! A map on presentation relations extends to the ambient module after
reduction by a maximal ideal exactly when it kills the reduced kernel. -/

universe u v w t

theorem vectorMap_extend_of_ker_le
    {k : Type u} [Field k]
    {K : Type v} [AddCommGroup K] [Module k K]
    {F : Type w} [AddCommGroup F] [Module k F]
    {N : Type t} [AddCommGroup N] [Module k N]
    (f : K →ₗ[k] F) (g : K →ₗ[k] N) (h : f.ker ≤ g.ker) :
    ∃ l : F →ₗ[k] N, ∀ x, l (f x) = g x := by
  let r := (f.ker.liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨p, hp⟩ := f.range.subtype.exists_leftInverse_of_injective f.range.ker_subtype
  refine ⟨r.comp p, fun x => ?_⟩
  have hp' : p (f x) = f.rangeRestrict x := LinearMap.congr_fun hp (f.rangeRestrict x)
  change r (p (f x)) = g x
  rw [hp']
  change f.ker.liftQ g h (f.quotKerEquivRange.symm ⟨f x, _⟩) = g x
  rw [LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]

theorem residue_linear_extension
    {B : Type u} [CommRing B] (m : Ideal B) [m.IsMaximal]
    {K : Type v} [AddCommGroup K] [Module B K]
    {F : Type w} [AddCommGroup F] [Module B F]
    {N : Type t} [AddCommGroup N] [Module B N] [Module (B ⧸ m) N]
    [IsScalarTower B (B ⧸ m) N]
    (f : K →ₗ[B] F) (g : K →ₗ[B] N)
    (h : ∀ x, f x ∈ m • (⊤ : Submodule B F) → g x = 0) :
    ∃ l : F →ₗ[B] N, ∀ x, l (f x) = g x := by
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  let P : Submodule B K := m • ⊤
  let Q : Submodule B F := m • ⊤
  have hg : P ≤ g.ker := by
    apply Submodule.smul_le.mpr
    intro r hr x _
    apply h
    rw [map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  let fbar := f.reduceModIdeal m
  let gbar : (K ⧸ P) →ₗ[B ⧸ m] N :=
    (P.liftQ g hg).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have hk : fbar.ker ≤ gbar.ker := by
    intro x hx
    obtain ⟨z, rfl⟩ := P.mkQ_surjective x
    change Submodule.Quotient.mk (p := Q) (f z) = 0 at hx
    exact h z ((Submodule.Quotient.mk_eq_zero Q).mp hx)
  obtain ⟨l, hl⟩ := vectorMap_extend_of_ker_le fbar gbar hk
  refine ⟨(l.restrictScalars B).comp Q.mkQ, fun x => ?_⟩
  exact hl (P.mkQ x)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ResidueLinearExtension
