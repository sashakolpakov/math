import OAI.NumberTheory.Quaternion.Arithmetic.UnitsWeakApproximation
import Mathlib.GroupTheory.Commutator.Finite

/-! # Commutator Approximation -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.CommutatorApproximation

noncomputable section

/-! Dense approximation in an ambient group approximates commutators
by commutators of rational points. A finite-product version restricts
the resulting approximation to specified subgroups. -/

open scoped Classical commutatorElement
open Set

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

theorem commutator_le_closure_of_denseRange (f : G →* H) (hf : DenseRange f)
    (Γ : Subgroup G) (hΓ : commutator G ≤ Γ) :
    commutator H ≤ (Γ.map f).topologicalClosure := by
  rw [commutator_eq_closure]
  apply (Subgroup.closure_le ((Γ.map f).topologicalClosure)).mpr
  rintro z ⟨x, y, rfl⟩
  have hc : Continuous (fun p : H × H => ⁅p.1, p.2⁆) := by
    simp only [commutatorElement_def]
    exact ((continuous_fst.mul continuous_snd).mul continuous_fst.inv).mul continuous_snd.inv
  apply (hf.prodMap hf).induction_on
    (p := fun p : H × H => ⁅p.1, p.2⁆ ∈ (Γ.map f).topologicalClosure) (x, y)
    ((Γ.map f).isClosed_topologicalClosure.preimage hc)
  rintro ⟨a, b⟩
  apply (Γ.map f).le_topologicalClosure
  refine ⟨⁅a, b⁆, hΓ ?_, map_commutatorElement f a b⟩
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

variable {ι : Type*} [Finite ι] {L : ι → Type*} [∀ i, Group (L i)]
  [∀ i, TopologicalSpace (L i)] [∀ i, IsTopologicalGroup (L i)]

def subgroupPiDiagonal (f : ∀ i, G →* L i) (Γ : Subgroup G) (Λ : ∀ i, Subgroup (L i))
    (hm : ∀ (i : ι) (g : G), g ∈ Γ → f i g ∈ Λ i) : Γ →* (∀ i, Λ i) :=
  MonoidHom.pi (fun i => ((f i).comp Γ.subtype).codRestrict (Λ i) (fun g => hm i g.val g.property))

theorem denseRange_subgroupPiDiagonal_of_commutators (f : ∀ i, G →* L i)
    (hd : DenseRange (fun g : G => fun i => f i g))
    (Γ : Subgroup G) (hΓ : commutator G ≤ Γ)
    (Λ : ∀ i, Subgroup (L i)) (hΛ : ∀ i, Λ i ≤ commutator (L i))
    (hm : ∀ (i : ι) (g : G), g ∈ Γ → f i g ∈ Λ i) :
    DenseRange (subgroupPiDiagonal f Γ Λ hm) := by
  let e : (∀ i, Λ i) → (∀ i, L i) := fun x i => (x i).val
  have he : Topology.IsInducing e := Topology.IsInducing.piMap
    (fun _ => Topology.IsInducing.subtypeVal)
  rw [DenseRange, he.dense_iff]
  intro x
  have hx : e x ∈ commutator (∀ i, L i) := by
    have hp : Subgroup.pi Set.univ (fun i => commutator (L i)) = commutator (∀ i, L i) := by
      simpa only [← commutator_def, Subgroup.pi_top] using
        (Subgroup.commutator_pi_pi_of_finite (fun i => (⊤ : Subgroup (L i)))
          (fun i => (⊤ : Subgroup (L i)))).symm
    rw [← hp]
    exact fun i _ => hΛ i (x i).property
  have hmemb := commutator_le_closure_of_denseRange (MonoidHom.pi f) hd Γ hΓ hx
  have hr : e '' Set.range (subgroupPiDiagonal f Γ Λ hm) =
      (Γ.map (MonoidHom.pi f) : Set (∀ i, L i)) := by
    ext y
    constructor
    · rintro ⟨z, ⟨g, rfl⟩, rfl⟩
      exact ⟨g.val, g.property, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨subgroupPiDiagonal f Γ Λ hm ⟨g, hg⟩, Set.mem_range_self _, rfl⟩
  rw [hr]
  exact hmemb

end

end OAI.NumberTheory.Quaternion.Arithmetic.CommutatorApproximation
