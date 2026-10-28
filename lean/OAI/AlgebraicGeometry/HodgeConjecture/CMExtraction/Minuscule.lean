import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Operators
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters

/-! # Minuscule -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Minuscule

noncomputable section

/-! The GL3 minuscule operators map to the exact operators in the chosen
native TateComparison action, by uniqueness of their raw double-coset kernels. -/

open scoped Classical TensorProduct

namespace Local

variable (q : ℕ) [Fact q.Prime]

def gl3MinusculeRepresentative (k : Fin 4) : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q :=
  AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (fun i => AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ (if i.val < k.val then (1 : ℤ) else 0))

theorem activeGL3_minuscule_representative {s : ℕ} (v : Fin s) (k : Fin 4) :
    CosetsKernel.Local.activeGL3Embedding q v (gl3MinusculeRepresentative q k) =
      AbelianScheme.TateComparison.HeckeKernel.representative s q (Intrinsic.MinusculeParameters.activeMinusculeType v k) := by
  apply Prod.ext
  · funext w
    change (if w = v then gl3MinusculeRepresentative q k else 1) =
      AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (fun i => AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ (if w = v ∧ i.val < k.val then (1 : ℤ) else 0))
    by_cases hw : w = v
    · simp only [hw, ite_eq_left, true_and, gl3MinusculeRepresentative]
    · simp only [hw, false_and, ite_false, zpow_zero]
      apply Units.ext
      simp [AbelianScheme.TateComparison.HeckeKernel.diagonalUnit]
  · change (1 : ℚ_[q]ˣ) = AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ (0 : ℤ)
    simp

def gl3MinusculeHecke (k : Fin 4) : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) :=
  Operators.Local.rawGL3Hecke q (gl3MinusculeRepresentative q k)

end Local

namespace Intrinsic
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Minuscule.Local

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem native_minuscule_GL3 (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (hA : A.IsRealization D hg hq hIsogenyQuotient) (k : Fin 4) :
    CosetsKernel.Local.activeGL3HeckeMap q D.reference.distinguished (Local.gl3MinusculeHecke q k) =
      Intrinsic.MinusculeParameters.nativeMinusculeHecke D A k := by
  apply AbelianScheme.TateComparison.HeckeKernel.rawDoubleCoset_unique (AbelianScheme.TateComparison.HeckeKernel.integralLevel s q)
    (Operators.Local.activeGL3HeckeMap_isRaw q D.reference.distinguished (Operators.Local.rawGL3Hecke_isRaw q _))
  rw [Local.activeGL3_minuscule_representative]
  exact hA.basis _

/-- Restriction of the given full character along the actual GL3 embedding. -/
def nativeGL3Character (F : Type*) [Field F] [Algebra ℚ F]
    (χ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F) :
    F ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) →ₐ[F] F :=
  χ.comp (Algebra.TensorProduct.map (AlgHom.id F F)
    (CosetsKernel.Local.activeGL3HeckeMap q D.reference.distinguished))

theorem nativeGL3Character_minuscule (F : Type*) [Field F] [Algebra ℚ F]
    (χ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (hA : A.IsRealization D hg hq hIsogenyQuotient) (k : Fin 4) :
    nativeGL3Character D F χ (1 ⊗ₜ[ℚ] Local.gl3MinusculeHecke q k) =
      χ (1 ⊗ₜ[ℚ] Intrinsic.MinusculeParameters.nativeMinusculeHecke D A k) := by
  change χ (1 ⊗ₜ[ℚ] CosetsKernel.Local.activeGL3HeckeMap q D.reference.distinguished (Local.gl3MinusculeHecke q k)) = _
  rw [native_minuscule_GL3 D A hg hq hIsogenyQuotient hA]

end Intrinsic

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Minuscule
