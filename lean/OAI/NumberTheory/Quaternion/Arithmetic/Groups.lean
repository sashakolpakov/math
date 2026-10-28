import OAI.NumberTheory.Quaternion.Arithmetic.ApproximationTopology

/-! # Groups -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.Groups

noncomputable section

/-! S-integral rational points and the finite-product form of Arithmetic.
The arithmetic subgroups are defined by their actual local integrality
conditions. No density assertion is part of their data. -/

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)

/-- Rational points integral at every place outside R, in the fixed matrix
realization. At infinite places the integral subgroup is the whole group. -/
def sIntegralPoints (R : Set (LocalAdeles.Place F)) : Subgroup G.RationalPoints where
  carrier := {g | ∀ v, v ∉ R → LocalAdeles.diagonalLocal G v g ∈ LocalAdeles.integralLocalSubgroup G v}
  one_mem' := by intro v _; simp
  mul_mem' := by
    intro g h hg hh v hv
    simpa only [map_mul] using (LocalAdeles.integralLocalSubgroup G v).mul_mem (hg v hv) (hh v hv)
  inv_mem' := by
    intro g hg v hv
    simpa only [map_inv] using (LocalAdeles.integralLocalSubgroup G v).inv_mem (hg v hv)

theorem sIntegralPoints_mono {R R' : Set (LocalAdeles.Place F)} (h : R ⊆ R') :
    sIntegralPoints G R ≤ sIntegralPoints G R' := by
  intro g hg v hv
  exact hg v (fun hR => hv (h hR))

variable (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S))

/-- The S ∪ T-integral rational points, indexed by the places of T outside S. -/
def arithmeticSubgroup : Subgroup G.RationalPoints where
  carrier := {g | ∀ v : ApproximationTopology.AwayPlace S, v ∉ T →
    LocalAdeles.diagonalLocal G v.val g ∈ LocalAdeles.integralLocalSubgroup G v.val}
  one_mem' := by intro v _; simp
  mul_mem' := by
    intro g h hg hh v hv
    simpa only [map_mul] using (LocalAdeles.integralLocalSubgroup G v.val).mul_mem (hg v hv) (hh v hv)
  inv_mem' := by
    intro g hg v hv
    simpa only [map_inv] using (LocalAdeles.integralLocalSubgroup G v.val).inv_mem (hg v hv)

theorem arithmeticSubgroup_eq_sIntegralPoints :
    arithmeticSubgroup G S T =
      sIntegralPoints G ((S : Set (LocalAdeles.Place F)) ∪ Subtype.val '' (T : Set (ApproximationTopology.AwayPlace S))) := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg v hv
    have hvS : v ∉ S := fun h => hv (Or.inl h)
    have hvT : (⟨v, hvS⟩ : ApproximationTopology.AwayPlace S) ∉ T :=
      fun h => hv (Or.inr ⟨⟨v, hvS⟩, h, rfl⟩)
    exact hg ⟨v, hvS⟩ hvT
  · intro hg v hv
    apply hg v.val
    rintro (hS | ⟨w, hw, heq⟩)
    · exact v.property hS
    · exact hv ((Subtype.ext heq : w = v) ▸ hw)

abbrev SelectedLocalProduct :=
  (v : (T : Set (ApproximationTopology.AwayPlace S))) → LocalAdeles.LocalPoints G v.val.val

def arithmeticProjection : arithmeticSubgroup G S T →* SelectedLocalProduct G S T where
  toFun g v := LocalAdeles.diagonalLocal G v.val.val g.val
  map_one' := by funext v; exact map_one (LocalAdeles.diagonalLocal G v.val.val)
  map_mul' g h := by funext v; exact map_mul (LocalAdeles.diagonalLocal G v.val.val) g.val h.val

/-- Strong approximation is precisely density of the S ∪ T-integral rational
points in every selected finite local product. -/
theorem strongApproximation_iff_arithmeticProjection_dense :
    DenseRange (LocalAdeles.diagonalAway G S) ↔
      ∀ T : Finset (ApproximationTopology.AwayPlace S), DenseRange (arithmeticProjection G S T) := by
  rw [ApproximationTopology.denseRange_diagonalAway_iff]
  constructor
  · intro h T a
    rw [mem_closure_iff]
    intro V hV ha
    obtain ⟨U, hU, hsub⟩ := isOpen_pi_iff'.mp hV a ha
    let U' : (v : ApproximationTopology.AwayPlace S) → Set (LocalAdeles.LocalPoints G v.val) :=
      fun v => if hv : v ∈ T then U ⟨v, hv⟩ else Set.univ
    have ho : ∀ v ∈ T, IsOpen (U' v) := by
      intro v hv
      simpa only [U', dite_eq_left hv] using (hU ⟨v, hv⟩).1
    have hn : ∀ v ∈ T, (U' v).Nonempty := by
      intro v hv
      refine ⟨a ⟨v, hv⟩, ?_⟩
      simpa only [U', dite_eq_left hv] using (hU ⟨v, hv⟩).2
    obtain ⟨g, hg⟩ := h T U' ho hn
    let γ : arithmeticSubgroup G S T := ⟨g, hg.2⟩
    refine ⟨arithmeticProjection G S T γ, hsub ?_, Set.mem_range_self γ⟩
    intro v _
    have hvT : v.val ∈ T := v.property
    have hv := hg.1 v.val hvT
    change LocalAdeles.diagonalLocal G v.val.val g ∈ U v
    simpa only [U', dite_eq_left hvT, LocalAdeles.diagonalAway_apply] using hv
  · intro h T U ho hn
    let V : Set (SelectedLocalProduct G S T) :=
      Set.pi Set.univ (fun v => U v.val)
    have hV : IsOpen V :=
      isOpen_set_pi (Set.toFinite Set.univ) (fun v _ => ho v.val v.property)
    have hVN : V.Nonempty := by
      refine ⟨fun v => (hn v.val v.property).choose, ?_⟩
      intro v _
      exact (hn v.val v.property).choose_spec
    obtain ⟨g, hg⟩ := (h T).exists_mem_open hV hVN
    refine ⟨g.val, ?_, g.property⟩
    intro v hv
    exact hg ⟨v, hv⟩ (Set.mem_univ _)

end

end OAI.NumberTheory.Quaternion.Arithmetic.Groups
