import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntermediateLattices

/-! # Bounded Lattice Subgroups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BoundedLatticeSubgroups.Construction

noncomputable section

section

/-!
For T = q^(-h)L the quotient T/L is killed by q^h. Consequently its
additive subgroups are exactly the bounded intermediate q-adic lattices.
-/

open scoped Pointwise

variable (q : ℕ) [Fact q.Prime] {d : ℕ}

abbrev qPowerSuperlattice (h : ℕ) (L : Submodule ℤ_[q] (Fin d → ℚ_[q])) :=
  SuperlatticeType.Construction.uniformizerPowerLattice (q : ℤ_[q]) PadicInt.irreducible_p (-(h : ℤ)) L

theorem mem_qPowerSuperlattice_iff (h : ℕ)
    (L : Submodule ℤ_[q] (Fin d → ℚ_[q])) (x : Fin d → ℚ_[q]) :
    x ∈ qPowerSuperlattice q h L ↔ (q : ℤ_[q]) ^ h • x ∈ L := by
  let z := (Units.mk0 (algebraMap ℤ_[q] ℚ_[q] (q : ℤ_[q]))
    (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.uniformizer_map_ne_zero PadicInt.irreducible_p)) ^ (-(h : ℤ))
  have hq : (q : ℚ_[q]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hleft (y : Fin d → ℚ_[q]) : (q : ℤ_[q]) ^ h • (z • y) = y := by
    rw [← algebraMap_smul ℚ_[q], map_pow, map_natCast]
    simp [z, Units.smul_def, smul_smul, hq]
  have hright (y : Fin d → ℚ_[q]) : z • ((q : ℤ_[q]) ^ h • y) = y := by
    rw [← algebraMap_smul ℚ_[q], map_pow, map_natCast]
    simp [z, Units.smul_def, smul_smul, hq]
  change x ∈ z • L ↔ _
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x z L).mp hx
    rwa [hleft]
  · intro hx
    exact (Submodule.mem_smul_pointwise_iff_exists x z L).mpr
      ⟨(q : ℤ_[q]) ^ h • x, hx, hright x⟩

theorem le_qPowerSuperlattice (h : ℕ) (L : Submodule ℤ_[q] (Fin d → ℚ_[q])) :
    L ≤ qPowerSuperlattice q h L := by
  intro x hx
  exact (mem_qPowerSuperlattice_iff q h L x).mpr (L.smul_mem _ hx)

instance qPowerSuperlattice_isLattice (h : ℕ)
    (L : Submodule ℤ_[q] (Fin d → ℚ_[q])) [Submodule.IsLattice ℚ_[q] L] :
    Submodule.IsLattice ℚ_[q] (qPowerSuperlattice q h L) := by
  unfold qPowerSuperlattice SuperlatticeType.Construction.uniformizerPowerLattice
  infer_instance

theorem qPowerSuperlattice_quotient_killed (h : ℕ)
    (L : Submodule ℤ_[q] (Fin d → ℚ_[q]))
    (x : qPowerSuperlattice q h L ⧸ L.comap (qPowerSuperlattice q h L).subtype) :
    (q : ℤ_[q]) ^ h • x = 0 := by
  obtain ⟨y, rfl⟩ := (L.comap (qPowerSuperlattice q h L).subtype).mkQ_surjective x
  rw [← map_smul]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (mem_qPowerSuperlattice_iff q h L y.val).mp y.property

/-- Actual subgroup choices, without extra scalar-stability or lattice
finiteness data, classify L <= M <= q^(-h)L. -/
def boundedLatticeSubgroupOrderIso (h : ℕ)
    (L : Submodule ℤ_[q] (Fin d → ℚ_[q])) :
    AddSubgroup (qPowerSuperlattice q h L ⧸
      L.comap (qPowerSuperlattice q h L).subtype) ≃o
      Set.Icc L (qPowerSuperlattice q h L) :=
  IntermediateLattices.Construction.latticeQuotientSubgroupOrderIso q L (qPowerSuperlattice q h L)
    (le_qPowerSuperlattice q h L) h (qPowerSuperlattice_quotient_killed q h L)

theorem bounded_subgroup_lattice_type_from_ElementaryDivisors (h : ℕ)
    (L : Submodule ℤ_[q] (Fin d → ℚ_[q])) [Submodule.IsLattice ℚ_[q] L]
    (H : AddSubgroup (qPowerSuperlattice q h L ⧸
      L.comap (qPowerSuperlattice q h L).subtype)) (h_ElementaryDivisors : ElementaryDivisors.Construction.ElementaryDivisorsInput.{0}) :
    let M := (boundedLatticeSubgroupOrderIso q h L H).val
    ∃! a : Fin d → ℕ,
      Antitone a ∧ (∀ i, a i ≤ h) ∧
      ∃ e : Module.Basis (Fin d) ℚ_[q] (Fin d → ℚ_[q]),
        L = Submodule.span ℤ_[q] (Set.range e) ∧
        M = LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ)) := by
  let M := boundedLatticeSubgroupOrderIso q h L H
  let : Submodule.IsLattice ℚ_[q] M.val := IntermediateLattices.Construction.intermediate_isLattice q L _ M
  exact SuperlatticeType.Construction.bounded_superlattice_type_from_ElementaryDivisors (q : ℤ_[q]) PadicInt.irreducible_p
    (R := ℤ_[q]) (K := ℚ_[q]) L M.val h M.property.1 M.property.2 h_ElementaryDivisors

end

/-!
The subgroup corresponding to an intermediate lattice M is canonically
isomorphic to M/L. Thus the ElementaryDivisors elementary module computed from M is the
type of the original subgroup, not just that of an auxiliary quotient.
-/

variable (q : ℕ) [Fact q.Prime] {d : ℕ}
  (L T : Submodule ℤ_[q] (Fin d → ℚ_[q])) (hLT : L ≤ T) (h : ℕ)
  (hkilled : ∀ x : T ⧸ L.comap T.subtype, (q : ℤ_[q]) ^ h • x = 0)
  (H : AddSubgroup (T ⧸ L.comap T.subtype))

theorem mem_subgroup_lattice_iff (x : T) :
    x.val ∈ (IntermediateLattices.Construction.latticeQuotientSubgroupOrderIso q L T hLT h hkilled H).val ↔
      (L.comap T.subtype).mkQ x ∈ H := by
  change (∃ y : T, (L.comap T.subtype).mkQ y ∈ H ∧ y.val = x.val) ↔ _
  constructor
  · rintro ⟨y, hy, he⟩
    have he' : y = x := Subtype.ext he
    rwa [he'] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

set_option backward.isDefEq.respectTransparency false in
def subgroupLatticeProjection :
    (IntermediateLattices.Construction.latticeQuotientSubgroupOrderIso q L T hLT h hkilled H).val →+ H where
  toFun x :=
    ⟨(L.comap T.subtype).mkQ
      ⟨x.val, (IntermediateLattices.Construction.latticeQuotientSubgroupOrderIso q L T hLT h hkilled H).property.2 x.property⟩,
      (mem_subgroup_lattice_iff q L T hLT h hkilled H _).mp x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := by
    apply Subtype.ext
    exact (L.comap T.subtype).mkQ.map_add
      ⟨x.val, (IntermediateLattices.Construction.latticeQuotientSubgroupOrderIso q L T hLT h hkilled H).property.2 x.property⟩
      ⟨y.val, (IntermediateLattices.Construction.latticeQuotientSubgroupOrderIso q L T hLT h hkilled H).property.2 y.property⟩

set_option backward.isDefEq.respectTransparency false in
theorem subgroupLatticeProjection_surjective :
    Function.Surjective (subgroupLatticeProjection q L T hLT h hkilled H) := by
  intro y
  obtain ⟨x, hx⟩ := (L.comap T.subtype).mkQ_surjective y.val
  have hm : x.val ∈ (IntermediateLattices.Construction.latticeQuotientSubgroupOrderIso q L T hLT h hkilled H).val :=
    (mem_subgroup_lattice_iff q L T hLT h hkilled H x).mpr (hx ▸ y.property)
  exact ⟨⟨x.val, hm⟩, Subtype.ext hx⟩

set_option backward.isDefEq.respectTransparency false in
theorem subgroupLatticeProjection_ker :
    (subgroupLatticeProjection q L T hLT h hkilled H).ker =
      (L.comap (IntermediateLattices.Construction.latticeQuotientSubgroupOrderIso q L T hLT h hkilled H).val.subtype).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, Subtype.ext_iff]
  change (L.comap T.subtype).mkQ
    ⟨x.val, (IntermediateLattices.Construction.latticeQuotientSubgroupOrderIso q L T hLT h hkilled H).property.2 x.property⟩ = 0 ↔
      x.val ∈ L
  exact Submodule.Quotient.mk_eq_zero _

def subgroupLatticeQuotientEquiv :
    (IntermediateLattices.Construction.latticeQuotientSubgroupOrderIso q L T hLT h hkilled H).val ⧸
      (L.comap (IntermediateLattices.Construction.latticeQuotientSubgroupOrderIso q L T hLT h hkilled H).val.subtype).toAddSubgroup ≃+ H :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (subgroupLatticeProjection_ker q L T hLT h hkilled H).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (subgroupLatticeProjection q L T hLT h hkilled H)
      (subgroupLatticeProjection_surjective q L T hLT h hkilled H))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BoundedLatticeSubgroups.Construction
