import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Dense Open Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseOpenRestriction.TestTransport

noncomputable section

/-! Restricting a dense product homomorphism to an open level in the
second factor leaves a dense first-factor image. -/

open scoped Classical

variable {Γ G H : Type*} [Group Γ] [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  (f : Γ →* G × H) (L : OpenSubgroup H)

def openSecondFactor : Subgroup Γ := L.toSubgroup.comap ((MonoidHom.snd G H).comp f)

def restrictedFirstFactor : openSecondFactor f L →* G :=
  ((MonoidHom.fst G H).comp f).comp (openSecondFactor f L).subtype

theorem restrictedFirstFactor_dense (hf : DenseRange f) :
    DenseRange (restrictedFirstFactor f L) := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨γ, hγ⟩ := hf.exists_mem_open (hU.prod L.isOpen) ⟨(x, 1), hx, L.one_mem⟩
  exact ⟨(f γ).1, hγ.1, ⟨⟨γ, hγ.2⟩, rfl⟩⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseOpenRestriction.TestTransport
