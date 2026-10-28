import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockLatticeCosets
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TypedLatticeChoices

/-! # Block Hecke Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction

noncomputable section

section

/-!
Raw GL3 double-coset support is exactly the set of lattices with the
prescribed Smith powers. The inverse representative yields q^(-a_i),
matching the kernel quotient convention proved in the preceding modules.
-/

open _root_.Module

open OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction

variable (q : ℕ) [Fact q.Prime]

def blockDiagonal (a : Fin 3 → ℤ) : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q] :=
  TateComparison.HeckeKernel.diagonalUnit (fun i => TateComparison.HeckeKernel.qUnit q ^ a i)

theorem blockDiagonal_val (a : Fin 3 → ℤ) :
    (blockDiagonal q a).val = Matrix.diagonal (fun i => (q : ℚ_[q]) ^ a i) := by
  simp only [blockDiagonal, TateComparison.HeckeKernel.diagonalUnit, Units.val_zpow_eq_zpow_val,
    TateComparison.HeckeKernel.qUnit, Units.val_mk0]

theorem blockDiagonal_inv (a : Fin 3 → ℤ) :
    (blockDiagonal q a)⁻¹ = blockDiagonal q (fun i => -a i) := by
  apply Units.ext
  change Matrix.diagonal (fun i => (((TateComparison.HeckeKernel.qUnit q ^ a i)⁻¹ : ℚ_[q]ˣ) : ℚ_[q])) = _
  simp [blockDiagonal, TateComparison.HeckeKernel.diagonalUnit, zpow_neg]

abbrev standardBlockLattice : Submodule ℤ_[q] (Fin 3 → ℚ_[q]) :=
  Submodule.span ℤ_[q] (Set.range (Pi.basisFun ℚ_[q] (Fin 3)))

instance standardBlockLattice_isLattice : Submodule.IsLattice ℚ_[q] (standardBlockLattice q) :=
  Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.basis_span_isLattice _

theorem block_smith_iff_factorization
    (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) (b : Fin 3 → ℤ) :
    (∃ e : BlockLatticeCosets.Construction.BlockBasis q,
      standardBlockLattice q = Submodule.span ℤ_[q] (Set.range e) ∧
      (BlockLatticeCosets.Construction.matrixBlockLattice q g).val = LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e b) ↔
    ∃ U V : Matrix.GeneralLinearGroup (Fin 3) ℤ_[q],
      g = Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) U *
        blockDiagonal q b * Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) V := by
  constructor
  · rintro ⟨e, heL, heM⟩
    let s := Pi.basisFun ℚ_[q] (Fin 3)
    let p := Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.powerBasis (q : ℤ_[q]) PadicInt.irreducible_p e b
    obtain ⟨U, hU⟩ := Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.integral_basis_change s e heL
    have hp : Submodule.span ℤ_[q] (Set.range p) =
        Submodule.span ℤ_[q] (Set.range (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis g)) := by
      rw [← LatticeBounds.Construction.diagonalLattice_eq_powerBasis_span (q : ℤ_[q]) PadicInt.irreducible_p]
      exact heM.symm
    obtain ⟨V, hV⟩ := Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.integral_basis_change p (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis g) hp
    refine ⟨U, V, ?_⟩
    apply Units.ext
    change g.val = U.val.map (algebraMap ℤ_[q] ℚ_[q]) *
      (blockDiagonal q b).val * V.val.map (algebraMap ℤ_[q] ℚ_[q])
    rw [blockDiagonal_val]
    calc
      g.val = s.toMatrix (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis g) := (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.standard_toMatrix_matrixBasis g).symm
      _ = s.toMatrix e * e.toMatrix p * p.toMatrix (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis g) := by
        rw [s.toMatrix_mul_toMatrix, s.toMatrix_mul_toMatrix]
      _ = _ := by rw [hU, hV, Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.toMatrix_powerBasis]; simp only [map_natCast]
  · rintro ⟨U, V, hg⟩
    have hm := congrArg Units.val hg
    change g.val = U.val.map (algebraMap ℤ_[q] ℚ_[q]) *
      (blockDiagonal q b).val * V.val.map (algebraMap ℤ_[q] ℚ_[q]) at hm
    rw [blockDiagonal_val] at hm
    exact Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrix_factorization_lattices (q : ℤ_[q]) PadicInt.irreducible_p g b U V
      (by simpa only [map_natCast] using hm)

/-- Membership in the raw support is exactly the simultaneous lattice
formula with the negative kernel exponents. -/
theorem raw_block_support_mk_iff_smith
    (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) (a : Fin 3 → ℕ) :
    QuotientGroup.mk g ∈ Hecke.Construction.rawRightCosetSupport (BlockLatticeCosets.Construction.blockIntegralLevel q)
      (blockDiagonal q (fun i => (a i : ℤ))) ↔
    ∃ e : BlockLatticeCosets.Construction.BlockBasis q,
      standardBlockLattice q = Submodule.span ℤ_[q] (Set.range e) ∧
      (BlockLatticeCosets.Construction.matrixBlockLattice q g).val = LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ)) := by
  rw [Hecke.Construction.rawRightCosetSupport_mk_iff, block_smith_iff_factorization, blockDiagonal_inv]
  constructor
  · rintro ⟨k, l, hg⟩
    obtain ⟨U, hU⟩ := k.property
    obtain ⟨V, hV⟩ := l.property
    exact ⟨U, V, by simpa only [hU, hV] using hg⟩
  · rintro ⟨U, V, hg⟩
    exact ⟨⟨_, ⟨U, rfl⟩⟩, ⟨_, ⟨V, rfl⟩⟩, hg⟩

theorem raw_block_support_iff_smith
    (x : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q] ⧸ BlockLatticeCosets.Construction.blockIntegralLevel q) (a : Fin 3 → ℕ) :
    x ∈ Hecke.Construction.rawRightCosetSupport (BlockLatticeCosets.Construction.blockIntegralLevel q) (blockDiagonal q (fun i => (a i : ℤ))) ↔
    ∃ e : BlockLatticeCosets.Construction.BlockBasis q,
      standardBlockLattice q = Submodule.span ℤ_[q] (Set.range e) ∧
      (BlockLatticeCosets.Construction.blockLatticeCosetEquiv q x).val = LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ)) := by
  induction x using Quotient.inductionOn with
  | h g => exact raw_block_support_mk_iff_smith q g a

end

/-!
For one chosen rank-three block, raw inverse double-coset points are in
bijection with unmarked subgroups of the prescribed elementary type.
The bounds on exponents are derived as bounds on the actual lattices.
-/

variable (q : ℕ) [Fact q.Prime]

abbrev BlockSmithLatticeChoices (a : Fin 3 → ℕ) :=
  {M : BlockLatticeCosets.Construction.BlockLattice q // ∃ e : BlockLatticeCosets.Construction.BlockBasis q,
    standardBlockLattice q = Submodule.span ℤ_[q] (Set.range e) ∧
    M.val = LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ))}

abbrev BoundedBlockSmithChoices (h : ℕ) (a : Fin 3 → ℕ) :=
  {M : Set.Icc (standardBlockLattice q) (BoundedLatticeSubgroups.Construction.qPowerSuperlattice q h (standardBlockLattice q)) //
    ∃ e : BlockLatticeCosets.Construction.BlockBasis q,
      standardBlockLattice q = Submodule.span ℤ_[q] (Set.range e) ∧
      M.val = LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ))}

abbrev BlockSubgroupChoices (h : ℕ) (a : Fin 3 → ℕ) :=
  {H : AddSubgroup (TypedLatticeChoices.Construction.BoundedLatticeQuotient q h (standardBlockLattice q)) //
    Nonempty (H ≃+ (∀ i, ZMod (q ^ a i)))}

theorem smith_lattice_bounds (h : ℕ) (L M : Submodule ℤ_[q] (Fin 3 → ℚ_[q]))
    (a : Fin 3 → ℕ) (ha : ∀ i, a i ≤ h)
    (he : ∃ e : BlockLatticeCosets.Construction.BlockBasis q, L = Submodule.span ℤ_[q] (Set.range e) ∧
      M = LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ))) :
    L ≤ M ∧ M ≤ BoundedLatticeSubgroups.Construction.qPowerSuperlattice q h L := by
  obtain ⟨e, heL, heM⟩ := he
  constructor
  · rw [heL, heM, ← LatticeBounds.Construction.diagonalLattice_zero (q : ℤ_[q]) e]
    apply (LatticeBounds.Construction.diagonalLattice_le_iff (q : ℤ_[q]) PadicInt.irreducible_p e _ _).mpr
    intro i
    omega
  · change M ≤ SuperlatticeType.Construction.uniformizerPowerLattice (q : ℤ_[q]) PadicInt.irreducible_p (-(h : ℤ)) L
    rw [heL, heM, ← SuperlatticeType.Construction.diagonalLattice_const]
    apply (LatticeBounds.Construction.diagonalLattice_le_iff (q : ℤ_[q]) PadicInt.irreducible_p e _ _).mpr
    intro i
    exact neg_le_neg (Int.ofNat_le.mpr (ha i))

def rawBlockSmithChoicesEquiv (a : Fin 3 → ℕ) :
    Hecke.Construction.rawRightCosetSupport (BlockLatticeCosets.Construction.blockIntegralLevel q) (blockDiagonal q (fun i => (a i : ℤ))) ≃
      BlockSmithLatticeChoices q a :=
  (BlockLatticeCosets.Construction.blockLatticeCosetEquiv q).subtypeEquiv (fun x => raw_block_support_iff_smith q x a)

def smithChoicesBoundedEquiv (h : ℕ) (a : Fin 3 → ℕ) (ha : ∀ i, a i ≤ h) :
    BlockSmithLatticeChoices q a ≃ BoundedBlockSmithChoices q h a where
  toFun M := ⟨⟨M.val.val, smith_lattice_bounds q h _ _ a ha M.property⟩, M.property⟩
  invFun M := ⟨⟨M.val.val, IntermediateLattices.Construction.intermediate_isLattice q _ _ M.val⟩, M.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Each raw coset is one subgroup choice, with coefficient one and no
subgroup marking. The exponent sign is fixed by the actual quotient. -/
def rawBlockSubgroupChoicesEquiv (h : ℕ) (a : Fin 3 → ℕ)
    (ha : ∀ i, a i ≤ h) (hdominant : Antitone a) (h_ElementaryDivisors : ElementaryDivisors.Construction.ElementaryDivisorsInput) :
    Hecke.Construction.rawRightCosetSupport (BlockLatticeCosets.Construction.blockIntegralLevel q) (blockDiagonal q (fun i => (a i : ℤ))) ≃
      BlockSubgroupChoices q h a :=
  ((rawBlockSmithChoicesEquiv q a).trans (smithChoicesBoundedEquiv q h a ha)).trans
    (TypedLatticeChoices.Construction.typedBoundedLatticeChoicesEquiv q h (standardBlockLattice q) a hdominant h_ElementaryDivisors).symm

theorem standardBoundedLatticeQuotient_finite (h : ℕ) :
    Finite (TypedLatticeChoices.Construction.BoundedLatticeQuotient q h (standardBlockLattice q)) := by
  have heM : BoundedLatticeSubgroups.Construction.qPowerSuperlattice q h (standardBlockLattice q) =
      LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) (Pi.basisFun ℚ_[q] (Fin 3)) (fun i => -((fun _ => h) i : ℤ)) :=
    (SuperlatticeType.Construction.diagonalLattice_const (q : ℤ_[q]) PadicInt.irreducible_p _ (-(h : ℤ))).symm
  exact Finite.of_equiv (∀ _ : Fin 3, ZMod (q ^ h))
    (Superlattice.Construction.superlatticeQuotientEquiv q (standardBlockLattice q)
      (BoundedLatticeSubgroups.Construction.qPowerSuperlattice q h (standardBlockLattice q)) (BoundedLatticeSubgroups.Construction.le_qPowerSuperlattice q h _)
      (Pi.basisFun ℚ_[q] (Fin 3)) (fun _ => h) rfl heM).symm.toEquiv

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction
