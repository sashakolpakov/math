import OAI.NumberTheory.Quaternion.Arithmetic.MinkowskiLocalProjections

/-! # Compact Integral Values -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.CompactIntegralValues

noncomputable section

/-! A fixed denominator and a compact archimedean bound leave only
finitely many rational values. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding Set

variable {F : Type} [Field F] [NumberField F]

theorem finite_rational_values_in_compact (d : F) (hd : d ≠ 0)
    (C : Set (mixedSpace F)) (hC : IsCompact C) :
    {x : F | d * x ∈ (algebraMap (𝓞 F) F).range ∧ mixedEmbedding F x ∈ C}.Finite := by
  let L := mixedEmbedding.integerLattice F
  let : DiscreteTopology L.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (mixedEmbedding.integerLattice F))
  let f : F → mixedSpace F := fun x => mixedEmbedding F (d * x)
  have hf : Function.Injective f := fun x y h =>
    mul_left_cancel₀ hd ((mixedEmbedding_injective F) h)
  have hLc : IsClosed (L : Set (mixedSpace F)) :=
    AddSubgroup.isClosed_of_discreteTopology (U := L.toAddSubgroup)
  have hLd : IsDiscrete (L : Set (mixedSpace F)) :=
    (SetLike.isDiscrete_iff_discreteTopology (s := L)).mpr inferInstance
  let D := (fun y : mixedSpace F => mixedEmbedding F d * y) '' C
  have hD : IsCompact D := hC.image (continuous_const.mul continuous_id)
  have hfinite : (D ∩ (L : Set (mixedSpace F))).Finite :=
    (hD.inter_right hLc).finite (hLd.mono inter_subset_right)
  apply (hfinite.preimage hf.injOn).subset
  intro x hx
  constructor
  · exact ⟨mixedEmbedding F x, hx.2, (map_mul (mixedEmbedding F) d x).symm⟩
  · obtain ⟨u, hu⟩ := hx.1
    exact ⟨u, congrArg (mixedEmbedding F) hu⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.CompactIntegralValues
