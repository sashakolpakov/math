import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Split Module Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SplitModuleKernel

noncomputable section

/-! A map between direct summands can be expressed by equations on the ambient modules, preserving its actual kernel. -/

universe u

variable (R : Type u) [CommRing R]
variable (M F : Type u) [AddCommGroup M] [Module R M] [AddCommGroup F] [Module R F]

structure SplitModuleEmbedding where
  inclusion : M →ₗ[R] F
  projection : F →ₗ[R] M
  split : projection.comp inclusion = LinearMap.id

variable {R M F}

theorem SplitModuleEmbedding.projection_inclusion (P : SplitModuleEmbedding R M F) (x : M) :
    P.projection (P.inclusion x) = x := congrArg (fun f : M →ₗ[R] M => f x) P.split

theorem SplitModuleEmbedding.inclusion_injective (P : SplitModuleEmbedding R M F) :
    Function.Injective P.inclusion := Function.LeftInverse.injective P.projection_inclusion

def SplitModuleEmbedding.baseChange (P : SplitModuleEmbedding R M F)
    (A : Type u) [CommRing A] [Algebra R A] :
    SplitModuleEmbedding A (TensorProduct R A M) (TensorProduct R A F) where
  inclusion := P.inclusion.baseChange A
  projection := P.projection.baseChange A
  split := by rw [← LinearMap.baseChange_comp, P.split, LinearMap.baseChange_id]

variable {N G : Type u} [AddCommGroup N] [Module R N] [AddCommGroup G] [Module R G]

def splitModuleKernelEquation (P : SplitModuleEmbedding R M F)
    (Q : SplitModuleEmbedding R N G) (f : M →ₗ[R] N) : F →ₗ[R] G × F :=
  (Q.inclusion.comp (f.comp P.projection)).prod (LinearMap.id - P.inclusion.comp P.projection)

theorem splitModuleKernelEquation_mem (P : SplitModuleEmbedding R M F)
    (Q : SplitModuleEmbedding R N G) (f : M →ₗ[R] N) (x : F) :
    x ∈ (splitModuleKernelEquation P Q f).ker ↔
      f (P.projection x) = 0 ∧ P.inclusion (P.projection x) = x := by
  change (Q.inclusion (f (P.projection x)), x - P.inclusion (P.projection x)) = (0, 0) ↔ _
  rw [Prod.mk.injEq, sub_eq_zero, eq_comm (a := x)]
  have he : Q.inclusion (f (P.projection x)) = 0 ↔ f (P.projection x) = 0 := by
    simpa only [map_zero] using
      (Q.inclusion_injective.eq_iff :
        Q.inclusion (f (P.projection x)) = Q.inclusion 0 ↔ f (P.projection x) = 0)
  exact and_congr he Iff.rfl

def splitModuleKernelEquiv (P : SplitModuleEmbedding R M F)
    (Q : SplitModuleEmbedding R N G) (f : M →ₗ[R] N) :
    f.ker ≃ₗ[R] (splitModuleKernelEquation P Q f).ker where
  toFun x := ⟨P.inclusion x, (splitModuleKernelEquation_mem P Q f _).mpr
    ⟨by rw [P.projection_inclusion]; exact x.property,
      congrArg P.inclusion (P.projection_inclusion x)⟩⟩
  invFun x := ⟨P.projection x, ((splitModuleKernelEquation_mem P Q f _).mp x.property).1⟩
  left_inv x := Subtype.ext (P.projection_inclusion x)
  right_inv x := Subtype.ext ((splitModuleKernelEquation_mem P Q f _).mp x.property).2
  map_add' x y := Subtype.ext (P.inclusion.map_add x y)
  map_smul' c x := Subtype.ext (P.inclusion.map_smul c x)

theorem finite_projective_exists_split [Module.Finite R M] [Module.Projective R M] :
    ∃ n : ℕ, Nonempty (SplitModuleEmbedding R M (Fin n → R)) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨i, hi⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
  exact ⟨n, ⟨⟨i, p, hi⟩⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SplitModuleKernel
