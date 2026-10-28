import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence

/-! # Lattice Division -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDivision.TorusTorsion

noncomputable section

section

/-! Division by N identifies the actual integral lattice modulo N
with N-torsion in its vector-space quotient, without choosing a basis. -/

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (Λ : Submodule ℤ V)
    (N : ℕ) [NeZero N]

def latticeMultipleSubgroup : AddSubgroup Λ := (nsmulAddMonoidHom (α := Λ) N).range

def latticeDivisionHom : Λ →+ TorsionCongruence.TorusTorsion.killedBy (V ⧸ Λ.toAddSubgroup) N where
  toFun := TorsionCongruence.TorusTorsion.latticeDivisionPoint Λ N
  map_zero' := by
    apply Subtype.ext
    change (QuotientAddGroup.mk ((N : ℚ)⁻¹ • (0 : V)) : V ⧸ Λ.toAddSubgroup) = 0
    rw [smul_zero]
    rfl
  map_add' v w := by
    apply Subtype.ext
    change (QuotientAddGroup.mk ((N : ℚ)⁻¹ • (v.val + w.val)) : V ⧸ Λ.toAddSubgroup) = _
    rw [smul_add, QuotientAddGroup.mk_add]
    rfl

theorem latticeDivisionHom_ker : (latticeDivisionHom Λ N).ker = latticeMultipleSubgroup Λ N := by
  ext v
  change TorsionCongruence.TorusTorsion.latticeDivisionPoint Λ N v = 0 ↔ ∃ w : Λ, N • w = v
  constructor
  · intro hv
    have hw : (N : ℚ)⁻¹ • v.val ∈ Λ :=
      (QuotientAddGroup.eq_zero_iff ((N : ℚ)⁻¹ • v.val)).mp (congrArg Subtype.val hv)
    exact ⟨⟨(N : ℚ)⁻¹ • v.val, hw⟩, Subtype.ext (TorsionCongruence.TorusTorsion.nat_smul_inverse N v.val)⟩
  · rintro ⟨w, rfl⟩
    apply Subtype.ext
    change (QuotientAddGroup.mk ((N : ℚ)⁻¹ • (N • w.val)) : V ⧸ Λ.toAddSubgroup) = 0
    rw [TorsionCongruence.TorusTorsion.inverse_smul_nat]
    exact (QuotientAddGroup.eq_zero_iff w.val).mpr w.property

def latticeDivisionEquiv :
    (Λ ⧸ latticeMultipleSubgroup Λ N) ≃+ TorsionCongruence.TorusTorsion.killedBy (V ⧸ Λ.toAddSubgroup) N :=
  (QuotientAddGroup.quotientAddEquivOfEq (latticeDivisionHom_ker Λ N)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (latticeDivisionHom Λ N)
      (TorsionCongruence.TorusTorsion.latticeDivisionPoint_surjective Λ N))

theorem latticeDivisionEquiv_mk (v : Λ) :
    latticeDivisionEquiv Λ N (QuotientAddGroup.mk v) = TorsionCongruence.TorusTorsion.latticeDivisionPoint Λ N v := rfl

end

/-! Group homomorphisms and isomorphisms induce their actual maps
modulo N. These will transport native integral level markings. -/

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

def multipleSubgroup (G : Type*) [AddCommGroup G] (N : ℕ) : AddSubgroup G :=
  (nsmulAddMonoidHom (α := G) N).range

def modNMap (N : ℕ) (f : G →+ H) : (G ⧸ multipleSubgroup G N) →+ (H ⧸ multipleSubgroup H N) :=
  QuotientAddGroup.map (multipleSubgroup G N) (multipleSubgroup H N) f (by
    rintro v ⟨w, rfl⟩
    exact ⟨f w, (map_nsmul f N w).symm⟩)

theorem modNMap_mk (N : ℕ) (f : G →+ H) (v : G) :
    modNMap N f (QuotientAddGroup.mk v) = QuotientAddGroup.mk (f v) := rfl

theorem multipleSubgroup_map (N : ℕ) (e : G ≃+ H) :
    (multipleSubgroup G N).map e.toAddMonoidHom = multipleSubgroup H N := by
  ext y
  constructor
  · rintro ⟨x, ⟨w, rfl⟩, rfl⟩
    exact ⟨e w, (map_nsmul e N w).symm⟩
  · rintro ⟨w, rfl⟩
    refine ⟨N • e.symm w, ⟨e.symm w, rfl⟩, ?_⟩
    exact (map_nsmul e N (e.symm w)).trans (congrArg (fun z => N • z) (e.apply_symm_apply w))

def modNEquiv (N : ℕ) (e : G ≃+ H) : (G ⧸ multipleSubgroup G N) ≃+ (H ⧸ multipleSubgroup H N) :=
  QuotientAddGroup.congr (multipleSubgroup G N) (multipleSubgroup H N) e (multipleSubgroup_map N e)

theorem modNEquiv_mk (N : ℕ) (e : G ≃+ H) (v : G) :
    modNEquiv N e (QuotientAddGroup.mk v) = QuotientAddGroup.mk (e v) := rfl

theorem modNEquiv_apply_eq_map (N : ℕ) (e : G ≃+ H) (x : G ⧸ multipleSubgroup G N) :
    modNEquiv N e x = modNMap N e.toAddMonoidHom x := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
  rfl

theorem modNMap_equiv_naturality
    {G' H' : Type*} [AddCommGroup G'] [AddCommGroup H']
    (N : ℕ) (eG : G ≃+ G') (eH : H ≃+ H') (f : G →+ H) (f' : G' →+ H')
    (hf : ∀ x, eH (f x) = f' (eG x)) (x : G ⧸ multipleSubgroup G N) :
    modNEquiv N eH (modNMap N f x) = modNMap N f' (modNEquiv N eG x) := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [modNMap_mk, modNEquiv_mk, modNEquiv_mk, modNMap_mk]
  exact congrArg QuotientAddGroup.mk (hf v)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDivision.TorusTorsion
