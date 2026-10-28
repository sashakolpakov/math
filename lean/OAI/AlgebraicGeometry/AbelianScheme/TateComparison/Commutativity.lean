import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Cartan
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Gelfand

/-! # Commutativity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity

noncomputable section

/-! Matrix transposition fixes the Cartan representatives. The Gelfand
criterion therefore proves commutativity of the actual spherical algebra. -/

open scoped Classical

section Transpose

variable {R : Type*} [CommRing R]

def matrixTranspose (g : Matrix.GeneralLinearGroup (Fin 3) R) :
    Matrix.GeneralLinearGroup (Fin 3) R where
  val := g.val.transpose
  inv := g.inv.transpose
  val_inv := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]

theorem matrixTranspose_mul (g f : Matrix.GeneralLinearGroup (Fin 3) R) :
    matrixTranspose (g * f) = matrixTranspose f * matrixTranspose g := by
  apply Units.ext
  exact Matrix.transpose_mul _ _

@[simp]
theorem matrixTranspose_inv (g : Matrix.GeneralLinearGroup (Fin 3) R) :
    matrixTranspose g⁻¹ = (matrixTranspose g)⁻¹ := rfl

theorem matrixTranspose_involutive : Function.Involutive (matrixTranspose (R := R)) := by
  intro g
  apply Units.ext
  rfl

variable (s : ℕ)

def splitTranspose (g : (Fin s → Matrix.GeneralLinearGroup (Fin 3) R) × Rˣ) :
    (Fin s → Matrix.GeneralLinearGroup (Fin 3) R) × Rˣ :=
  (fun v => matrixTranspose (g.1 v), g.2)

theorem splitTranspose_mul (g f : (Fin s → Matrix.GeneralLinearGroup (Fin 3) R) × Rˣ) :
    splitTranspose s (g * f) = splitTranspose s f * splitTranspose s g :=
  Prod.ext (funext fun v => matrixTranspose_mul (g.1 v) (f.1 v)) (mul_comm _ _)

@[simp]
theorem splitTranspose_inv (g : (Fin s → Matrix.GeneralLinearGroup (Fin 3) R) × Rˣ) :
    splitTranspose s g⁻¹ = (splitTranspose s g)⁻¹ := rfl

theorem splitTranspose_involutive : Function.Involutive (splitTranspose (R := R) s) := by
  intro g
  exact Prod.ext (funext fun v => matrixTranspose_involutive (g.1 v)) rfl

def splitInverseTranspose :
    ((Fin s → Matrix.GeneralLinearGroup (Fin 3) R) × Rˣ) ≃*
      ((Fin s → Matrix.GeneralLinearGroup (Fin 3) R) × Rˣ) where
  toFun g := splitTranspose s g⁻¹
  invFun g := splitTranspose s g⁻¹
  left_inv g := by
    dsimp only
    rw [splitTranspose_inv, splitTranspose_involutive, inv_inv]
  right_inv g := by
    dsimp only
    rw [splitTranspose_inv, splitTranspose_involutive, inv_inv]
  map_mul' g f := by rw [mul_inv_rev, splitTranspose_mul]

theorem splitInverseTranspose_involutive :
    Function.Involutive (splitInverseTranspose (R := R) s) :=
  (splitInverseTranspose s).left_inv

end Transpose

variable (s q : ℕ) [Fact q.Prime]

theorem splitTranspose_integralLevelMap
    (g : (Fin s → Matrix.GeneralLinearGroup (Fin 3) ℤ_[q]) × ℤ_[q]ˣ) :
    splitTranspose s (HeckeKernel.integralLevelMap s q g) =
      HeckeKernel.integralLevelMap s q (splitTranspose s g) := by
  apply Prod.ext
  · funext v
    apply Units.ext
    rfl
  · rfl

theorem splitTranspose_mem_level {g : HeckeKernel.SplitGroup s q} (hg : g ∈ HeckeKernel.integralLevel s q) :
    splitTranspose s g ∈ HeckeKernel.integralLevel s q := by
  obtain ⟨g, rfl⟩ := hg
  rw [splitTranspose_integralLevelMap]
  exact ⟨_, rfl⟩

theorem splitInverseTranspose_mem_level (g : HeckeKernel.SplitGroup s q) :
    splitInverseTranspose s g ∈ HeckeKernel.integralLevel s q ↔ g ∈ HeckeKernel.integralLevel s q := by
  have h (g : HeckeKernel.SplitGroup s q) (hg : g ∈ HeckeKernel.integralLevel s q) :
      splitInverseTranspose s g ∈ HeckeKernel.integralLevel s q :=
    splitTranspose_mem_level s q ((HeckeKernel.integralLevel s q).inv_mem hg)
  constructor
  · intro hg
    have hh := h _ hg
    rwa [splitInverseTranspose_involutive] at hh
  · exact h g

theorem splitTranspose_representative (t : Local.LocalType s) :
    splitTranspose s (HeckeKernel.representative s q t) = HeckeKernel.representative s q t := by
  apply Prod.ext
  · funext v
    apply Units.ext
    exact Matrix.diagonal_transpose _
  · rfl

theorem kernel_level_mul {G : Type*} [Group G] (U : Subgroup G)
    (T : HeckeKernel.SphericalHecke U) (l r : U) (g : G) :
    HeckeKernel.kernel U T (QuotientGroup.mk ((l : G) * g * (r : G))) = HeckeKernel.kernel U T (QuotientGroup.mk g) := by
  rw [QuotientGroup.mk_mul_of_mem _ r.property]
  exact HeckeKernel.kernel_u_smul U T l (QuotientGroup.mk g)

theorem kernel_splitTranspose (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (T : HeckeKernel.Hecke s q)
    (g : HeckeKernel.SplitGroup s q) :
    HeckeKernel.kernel (HeckeKernel.integralLevel s q) T (QuotientGroup.mk (splitTranspose s g)) =
      HeckeKernel.kernel (HeckeKernel.integralLevel s q) T (QuotientGroup.mk g) := by
  obtain ⟨t, l, r, hg⟩ := Cartan.exists_split_cartan q s hElementaryDivisors g
  let l' : HeckeKernel.integralLevel s q := ⟨splitTranspose s l.val, splitTranspose_mem_level s q l.property⟩
  let r' : HeckeKernel.integralLevel s q := ⟨splitTranspose s r.val, splitTranspose_mem_level s q r.property⟩
  rw [hg, splitTranspose_mul, splitTranspose_mul, splitTranspose_representative, ← mul_assoc]
  exact (kernel_level_mul _ T r' l' (HeckeKernel.representative s q t)).trans
    (kernel_level_mul _ T l r (HeckeKernel.representative s q t)).symm

/-- Commutativity is derived from ElementaryDivisors and transposition, for all elements
of the actual equivariant-endomorphism spherical algebra. -/
theorem spherical_mul_comm (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (S T : HeckeKernel.Hecke s q) :
    S * T = T * S := by
  apply Gelfand.spherical_commutative_of_involution (HeckeKernel.integralLevel s q) (splitInverseTranspose s)
    (splitInverseTranspose_mem_level s q) (splitInverseTranspose_involutive s)
  intro A g
  change HeckeKernel.kernel _ A (QuotientGroup.mk (splitTranspose s g⁻¹)⁻¹) = _
  rw [splitTranspose_inv, inv_inv]
  exact kernel_splitTranspose s q hElementaryDivisors A g

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity
