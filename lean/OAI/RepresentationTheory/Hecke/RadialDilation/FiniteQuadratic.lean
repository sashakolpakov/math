import OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur

/-! # Finite Quadratic -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteQuadratic.Realization

noncomputable section

/-! Concrete quadratic multiplier automorphisms of the finite-adelic test space. -/

open scoped Classical _root_.Topology _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem finiteQuadratic_mem (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    (fun x => D.finiteCharacter (QuadraticCommutator.Realization.ringQuadratic B x) * f.val x) ∈ Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι := by
  obtain ⟨hf, hc⟩ := (Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff f.val).mp f.property
  apply (Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr
  refine ⟨?_, hc.mul_left⟩
  apply IsLocallyConstant.mul _ hf
  apply (FiniteSchur.Realization.finiteCharacter_locallyConstant D).comp_continuous
  unfold QuadraticCommutator.Realization.ringQuadratic Matrix.mulVec dotProduct
  fun_prop

def finiteQuadratic (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) :
    Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι where
  toFun f := ⟨fun x => D.finiteCharacter (QuadraticCommutator.Realization.ringQuadratic B x) * f.val x,
    finiteQuadratic_mem D B f⟩
  invFun f := ⟨fun x => D.finiteCharacter (QuadraticCommutator.Realization.ringQuadratic (-B) x) * f.val x,
    finiteQuadratic_mem D (-B) f⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    change D.finiteCharacter (QuadraticCommutator.Realization.ringQuadratic (-B) x) *
      (D.finiteCharacter (QuadraticCommutator.Realization.ringQuadratic B x) * f.val x) = f.val x
    rw [QuadraticCommutator.Realization.ringQuadratic_neg, ← mul_assoc, ← D.finiteCharacter.map_add_eq_mul]
    simp
  right_inv f := by
    apply Subtype.ext
    funext x
    change D.finiteCharacter (QuadraticCommutator.Realization.ringQuadratic B x) *
      (D.finiteCharacter (QuadraticCommutator.Realization.ringQuadratic (-B) x) * f.val x) = f.val x
    rw [QuadraticCommutator.Realization.ringQuadratic_neg, ← mul_assoc, ← D.finiteCharacter.map_add_eq_mul]
    simp
  map_add' f h := by
    apply Subtype.ext
    funext x
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact mul_left_comm _ _ _

theorem finiteQuadratic_apply (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (finiteQuadratic D B f).val x = D.finiteCharacter (QuadraticCommutator.Realization.ringQuadratic B x) * f.val x := rfl

theorem finiteQuadratic_intertwines (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg D.finiteCharacter (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι)
      (QuadraticCommutator.Realization.ringUpper B hB) (finiteQuadratic D B) := by
  intro p q f h hh x
  rw [QuadraticCommutator.Realization.ringUpper_phase]
  change D.finiteCharacter (QuadraticCommutator.Realization.ringQuadratic B x) * h.val x =
    Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter (p + B *ᵥ q) q
      (fun y => D.finiteCharacter (QuadraticCommutator.Realization.ringQuadratic B y) * f.val y) x
  rw [hh]
  exact QuadraticCommutator.Realization.ringQuadratic_heisenberg D.finiteCharacter B hB p q x f.val

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteQuadratic.Realization
