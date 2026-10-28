import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Reduction Transport -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.ReductionTransport.Construction

noncomputable section

/-! Finite reductions pass to quotient groups and to saturated subgroups. -/

universe u v

variable {G : Type u} {H : Type v} [AddCommGroup G] [AddCommGroup H]

def nsmulQuotientMap (f : G →+ H) (n : ℕ) :
    G ⧸ (nsmulAddMonoidHom n : G →+ G).range →+
      H ⧸ (nsmulAddMonoidHom n : H →+ H).range :=
  QuotientAddGroup.map _ _ f (by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, (map_nsmul f n y).symm⟩)

theorem finite_nsmulQuotient_of_surjective (f : G →+ H) (hf : Function.Surjective f) (n : ℕ)
    [Finite (G ⧸ (nsmulAddMonoidHom n : G →+ G).range)] :
    Finite (H ⧸ (nsmulAddMonoidHom n : H →+ H).range) := by
  apply Finite.of_surjective (nsmulQuotientMap f n)
  intro y
  induction y using Quotient.inductionOn' with
  | h y =>
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨QuotientAddGroup.mk x, rfl⟩

theorem nsmulQuotientMap_subtype_injective (S : AddSubgroup G) (n : ℕ)
    (hs : ∀ x : G, n • x ∈ S → x ∈ S) :
    Function.Injective (nsmulQuotientMap S.subtype n) := by
  intro x y h
  induction x using Quotient.inductionOn' with
  | h x =>
    induction y using Quotient.inductionOn' with
    | h y =>
      change (QuotientAddGroup.mk (x : G) : G ⧸ (nsmulAddMonoidHom n : G →+ G).range) =
        QuotientAddGroup.mk (y : G) at h
      obtain ⟨z, hz⟩ := QuotientAddGroup.eq_iff_sub_mem.mp h
      change n • z = (x : G) - (y : G) at hz
      have hzS : z ∈ S := hs z (hz.symm ▸ S.sub_mem x.property y.property)
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      exact ⟨⟨z, hzS⟩, Subtype.ext hz⟩

theorem finite_nsmulQuotient_of_saturated (S : AddSubgroup G) (n : ℕ)
    (hs : ∀ x : G, n • x ∈ S → x ∈ S)
    [Finite (G ⧸ (nsmulAddMonoidHom n : G →+ G).range)] :
    Finite (S ⧸ (nsmulAddMonoidHom n : S →+ S).range) :=
  Finite.of_injective _ (nsmulQuotientMap_subtype_injective S n hs)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.ReductionTransport.Construction
