import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.Intersection
import Mathlib.RingTheory.Flat.Equalizer

/-! # Subspace Base I -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SubspaceBaseI.SubspaceBaseChange

noncomputable section

/-! Field extension preserves native kernels, intersections, and subspace dimensions in finite dimension. -/

open scoped TensorProduct

variable {K L V W I : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem kernel (f : V →ₗ[K] W) : f.ker.baseChange L = (f.baseChange L).ker :=
  (Module.Flat.ker_lTensor_eq L L f).symm

theorem sup (P Q : Submodule K V) :
    (P ⊔ Q).baseChange L = P.baseChange L ⊔ Q.baseChange L := by
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    change (1 : L) ⊗ₜ[K] (p + q) ∈ P.baseChange L ⊔ Q.baseChange L
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem _
      ((show P.baseChange L ≤ P.baseChange L ⊔ Q.baseChange L from le_sup_left)
        (P.tmul_mem_baseChange_of_mem (1 : L) hp))
      ((show Q.baseChange L ≤ P.baseChange L ⊔ Q.baseChange L from le_sup_right)
        (Q.tmul_mem_baseChange_of_mem (1 : L) hq))
  · exact sup_le (Submodule.baseChange_mono L le_sup_left) (Submodule.baseChange_mono L le_sup_right)

variable [FiniteDimensional K V]

theorem finrank (P : Submodule K V) : Module.finrank L (P.baseChange L) = Module.finrank K P :=
  (Submodule.toBaseChange.toLinearEquiv L P).finrank_eq.symm.trans Module.finrank_baseChange

theorem inf (P Q : Submodule K V) :
    (P ⊓ Q).baseChange L = P.baseChange L ⊓ Q.baseChange L := by
  apply Submodule.eq_of_le_of_finrank_eq
    (le_inf (Submodule.baseChange_mono L inf_le_left) (Submodule.baseChange_mono L inf_le_right))
  have hK := Submodule.finrank_sup_add_finrank_inf_eq P Q
  have hL := Submodule.finrank_sup_add_finrank_inf_eq (P.baseChange L) (Q.baseChange L)
  rw [← sup, SubspaceBaseChange.finrank, SubspaceBaseChange.finrank, SubspaceBaseChange.finrank] at hL
  rw [SubspaceBaseChange.finrank]
  omega

theorem finset_iInf (P : I → Submodule K V) (s : Finset I) :
    (⨅ i ∈ s, P i).baseChange L = ⨅ i ∈ s, (P i).baseChange L := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.iInf_insert, Finset.iInf_insert, inf, ih]

theorem iInf (P : I → Submodule K V) :
    (⨅ i, P i).baseChange L = ⨅ i, (P i).baseChange L := by
  obtain ⟨s, hs⟩ := Finite.Intersection.GeneralizedHecke.finite_intersection P
  apply le_antisymm
  · exact le_iInf fun i => Submodule.baseChange_mono L (iInf_le P i)
  · have hb : (⨅ i, (P i).baseChange L) ≤ ⨅ i ∈ s, (P i).baseChange L :=
      le_iInf fun i => le_iInf fun _ => iInf_le (fun j => (P j).baseChange L) i
    exact hb.trans_eq ((finset_iInf P s).symm.trans (congrArg (Submodule.baseChange L) hs))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SubspaceBaseI.SubspaceBaseChange
