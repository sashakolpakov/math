import OAI.NumberTheory.Quaternion.Arithmetic.FiniteIndex

/-! # Additive Generation Transport -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdditiveGenerationTransport

noncomputable section

/-! Transport of additive generation and character kernels through
actual multiplicative equivalences. -/

open scoped Classical

variable {K G H Z : Type*} [Field K] [Group G] [Group H] [Group Z]

theorem additive_generation_of_mulEquiv (e : G ≃* H)
    (h : Subgroup.closure (FiniteIndex.additiveParameterElements (K := K) (G := G)) = ⊤) :
    Subgroup.closure (FiniteIndex.additiveParameterElements (K := K) (G := H)) = ⊤ := by
  let U := Subgroup.closure (FiniteIndex.additiveParameterElements (K := K) (G := H))
  have hle : Subgroup.closure (FiniteIndex.additiveParameterElements (K := K) (G := G)) ≤ U.comap e.toMonoidHom := by
    apply (Subgroup.closure_le (U.comap e.toMonoidHom)).mpr
    rintro g ⟨u, t, rfl⟩
    exact Subgroup.subset_closure ⟨e.toMonoidHom.comp u, t, rfl⟩
  rw [h] at hle
  apply top_unique
  intro y _
  have hy := hle (Subgroup.mem_top (e.symm y))
  change e (e.symm y) ∈ U at hy
  simpa only [MulEquiv.apply_symm_apply] using hy

def characterKernelEquiv (e : G ≃* H) (φ : G →* Z) (ψ : H →* Z)
    (hc : ∀ g, ψ (e g) = φ g) : φ.ker ≃* ψ.ker where
  toFun g := ⟨e g.val, by
    apply MonoidHom.mem_ker.mpr
    rw [hc]
    exact MonoidHom.mem_ker.mp g.property⟩
  invFun h := ⟨e.symm h.val, by
    apply MonoidHom.mem_ker.mpr
    rw [← hc, MulEquiv.apply_symm_apply]
    exact MonoidHom.mem_ker.mp h.property⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g.val)
  right_inv h := Subtype.ext (e.apply_symm_apply h.val)
  map_mul' g h := Subtype.ext (e.map_mul g.val h.val)

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdditiveGenerationTransport
