import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantSymmetricEigenspaces
import Mathlib.Tactic.Module

/-! # Involution Spectral Decomposition -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.InvolutionSpectralDecomposition.Construction

noncomputable section

section

/-! An involution reversing a symmetric operator converts its negative
eigenspaces into positive eigenspaces. This gives the linear decomposition
underlying Iwasawa decomposition. -/

open _root_.Module.End

def positiveSpectralSubmodule
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : V →ₗ[ℝ] V) (P : Submodule ℝ V) : Submodule ℝ V :=
  ⨆ r : ℝ, ⨆ (_ : 0 < r), P ⊓ eigenspace A r

theorem positiveSpectralSubmodule_le
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : V →ₗ[ℝ] V) (P : Submodule ℝ V) : positiveSpectralSubmodule A P ≤ P :=
  iSup_le (fun _ => iSup_le (fun _ => inf_le_left))

theorem mem_positiveSpectralSubmodule
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : V →ₗ[ℝ] V) (P : Submodule ℝ V) {r : ℝ} (hr : 0 < r)
    {x : V} (hx : x ∈ P) (he : A x = r • x) : x ∈ positiveSpectralSubmodule A P :=
  Submodule.mem_iSup_of_mem r (Submodule.mem_iSup_of_mem hr ⟨hx, mem_eigenspace_iff.mpr he⟩)

theorem involution_spectral_decomposition
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A J : V →ₗ[ℝ] V) (hJ : Function.Involutive J)
    (hAJ : ∀ x, A (J x) = -J (A x))
    (P : Submodule ℝ V) (hspan : P = ⨆ r : ℝ, P ⊓ eigenspace A r)
    (hPJ : ∀ x ∈ P, J x ∈ P) :
    P = (P ⊓ (J + LinearMap.id).ker) ⊔
      (P ⊓ A.ker ⊓ (J - LinearMap.id).ker) ⊔ positiveSpectralSubmodule A P := by
  let K := P ⊓ (J + LinearMap.id).ker
  let Z := P ⊓ A.ker ⊓ (J - LinearMap.id).ker
  let N := positiveSpectralSubmodule A P
  change P = (K ⊔ Z) ⊔ N
  apply le_antisymm
  · conv_lhs => rw [hspan]
    apply iSup_le
    intro r x hx
    have hxP : x ∈ P := hx.1
    have hxA : A x = r • x := mem_eigenspace_iff.mp hx.2
    rcases lt_trichotomy 0 r with hr | hr | hr
    · exact Submodule.mem_sup_right (mem_positiveSpectralSubmodule A P hr hxP hxA)
    · subst r
      rw [zero_smul] at hxA
      let s := (2 : ℝ)⁻¹ • (x + J x)
      have hsP : s ∈ P := P.smul_mem _ (P.add_mem hxP (hPJ x hxP))
      have hsJ : J s = s := by
        simp only [s, map_smul, map_add, hJ x]
        module
      have hsA : A s = 0 := by
        simp only [s, map_smul, map_add, hxA, hAJ, map_zero, neg_zero, add_zero, smul_zero]
      have hs : s ∈ Z := ⟨⟨hsP, hsA⟩, by change J s - s = 0; rw [hsJ, sub_self]⟩
      have hk : x - s ∈ K := by
        refine ⟨P.sub_mem hxP hsP, ?_⟩
        change J (x - s) + (x - s) = 0
        rw [map_sub, hsJ]
        dsimp [s]
        module
      have ht := ((K ⊔ Z) ⊔ N).add_mem
        (Submodule.mem_sup_left (Submodule.mem_sup_left hk))
        (Submodule.mem_sup_left (Submodule.mem_sup_right hs))
      simpa only [sub_add_cancel] using ht
    · have hjN : J x ∈ N := by
        apply mem_positiveSpectralSubmodule A P (neg_pos.mpr hr) (hPJ x hxP)
        rw [hAJ, hxA, map_smul, neg_smul]
      have hk : x - J x ∈ K := by
        refine ⟨P.sub_mem hxP (hPJ x hxP), ?_⟩
        change J (x - J x) + (x - J x) = 0
        rw [map_sub, hJ x]
        abel
      have ht := ((K ⊔ Z) ⊔ N).add_mem
        (Submodule.mem_sup_left (Submodule.mem_sup_left hk)) (Submodule.mem_sup_right hjN)
      simpa only [sub_add_cancel] using ht
  · exact sup_le (sup_le inf_le_left (le_trans inf_le_left inf_le_left)) (positiveSpectralSubmodule_le A P)

theorem involution_symmetric_spectral_decomposition
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (A J : V →ₗ[ℝ] V) (hA : A.IsSymmetric) (hJ : Function.Involutive J)
    (hAJ : ∀ x, A (J x) = -J (A x))
    (P : Submodule ℝ V) (hPA : ∀ x ∈ P, A x ∈ P) (hPJ : ∀ x ∈ P, J x ∈ P) :
    P = (P ⊓ (J + LinearMap.id).ker) ⊔
      (P ⊓ A.ker ⊓ (J - LinearMap.id).ker) ⊔ positiveSpectralSubmodule A P :=
  involution_spectral_decomposition A J hJ hAJ P
    (InvariantSymmetricEigenspaces.Construction.symmetric_invariant_subspace_eigenspace_span A hA P hPA) hPJ

end

/-! An injective intertwining map identifies positive spectral
subspaces with their images. -/

open _root_.Module.End

theorem positiveSpectralSubmodule_range
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (A : W →ₗ[ℝ] W) (C : V →ₗ[ℝ] V) (f : V →ₗ[ℝ] W) (hf : Function.Injective f)
    (hAC : ∀ x, A (f x) = f (C x)) :
    positiveSpectralSubmodule A f.range = (positiveSpectralSubmodule C ⊤).map f := by
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr y hy
    obtain ⟨x, rfl⟩ := hy.1
    have hx : C x = r • x := by
      apply hf
      rw [← hAC, map_smul]
      exact mem_eigenspace_iff.mp hy.2
    exact ⟨x, mem_positiveSpectralSubmodule C ⊤ hr (Submodule.mem_top) hx, rfl⟩
  · suffices hle : positiveSpectralSubmodule C ⊤ ≤
        (positiveSpectralSubmodule A f.range).comap f from Submodule.map_le_iff_le_comap.mpr hle
    apply iSup_le
    intro r
    apply iSup_le
    intro hr x hx
    apply mem_positiveSpectralSubmodule A f.range hr ⟨x, rfl⟩
    rw [hAC, mem_eigenspace_iff.mp hx.2, map_smul]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.InvolutionSpectralDecomposition.Construction
