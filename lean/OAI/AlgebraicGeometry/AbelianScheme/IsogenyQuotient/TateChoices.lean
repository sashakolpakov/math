import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices

/-! # Tate Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateChoices.Construction

noncomputable section

/-!
Raw rank-three cosets classify subgroups of actual torsion after choosing
an integral Tate basis. The transport uses the proved evaluation residue
coordinates. It retains unmarked subgroup choices and their abstract
elementary type.
-/

def additiveSubgroupEquiv {G H : Type*} [AddGroup G] [AddGroup H] (e : G ≃+ H) :
    AddSubgroup G ≃ AddSubgroup H where
  toFun F := F.map e.toAddMonoidHom
  invFun F := F.map e.symm.toAddMonoidHom
  left_inv F := (AddSubgroup.map_symm_eq_iff_map_eq F (e := e)).mpr rfl
  right_inv F := (AddSubgroup.map_symm_eq_iff_map_eq F (e := e.symm)).mpr rfl

def typedAdditiveSubgroupEquiv {G H M : Type*} [AddGroup G] [AddGroup H] [AddGroup M]
    (e : G ≃+ H) :
    {F : AddSubgroup G // Nonempty (F ≃+ M)} ≃
      {F : AddSubgroup H // Nonempty (F ≃+ M)} :=
  (additiveSubgroupEquiv e).subtypeEquiv (fun F => by
    change Nonempty (F ≃+ M) ↔ Nonempty ((F.map e.toAddMonoidHom) ≃+ M)
    let eF := F.equivMapOfInjective e.toAddMonoidHom e.injective
    exact ⟨fun ⟨f⟩ => ⟨eF.symm.trans f⟩, fun ⟨f⟩ => ⟨eF.trans f⟩⟩)

theorem typedAdditiveSubgroupEquiv_membership
    {G H M : Type*} [AddGroup G] [AddGroup H] [AddGroup M]
    (e : G ≃+ H) (F : {F : AddSubgroup G // Nonempty (F ≃+ M)}) (x : G) :
    e x ∈ (typedAdditiveSubgroupEquiv e F).val ↔ x ∈ F.val := by
  change e x ∈ F.val.map e.toAddMonoidHom ↔ x ∈ F.val
  rw [AddSubgroup.mem_map_equiv, e.symm_apply_apply]

variable (q : ℕ) [Fact q.Prime]

def standardBoundedLatticeResidues (h : ℕ) :
    TypedLatticeChoices.Construction.BoundedLatticeQuotient q h (BlockHeckeChoices.Construction.standardBlockLattice q) ≃+ (Fin 3 → ZMod (q ^ h)) :=
  Superlattice.Construction.superlatticeQuotientEquiv q (BlockHeckeChoices.Construction.standardBlockLattice q)
    (BoundedLatticeSubgroups.Construction.qPowerSuperlattice q h (BlockHeckeChoices.Construction.standardBlockLattice q)) (BoundedLatticeSubgroups.Construction.le_qPowerSuperlattice q h _)
    (Pi.basisFun ℚ_[q] (Fin 3)) (fun _ => h) rfl
    (SuperlatticeType.Construction.diagonalLattice_const (q : ℤ_[q]) PadicInt.irreducible_p _ (-(h : ℤ))).symm

variable {H : Type*} [AddCommGroup H]
  (b : Module.Basis (Fin 3) ℤ_[q] (TateComparison.Add.Tate.Module (H := H) q))
  (hdiv : ∀ x : H, ∃ y, q • y = x) (h : ℕ)

def standardBoundedLatticeTorsionEquiv :
    TypedLatticeChoices.Construction.BoundedLatticeQuotient q h (BlockHeckeChoices.Construction.standardBlockLattice q) ≃+ TateComparison.Add.Tate.torsion q H h :=
  (standardBoundedLatticeResidues q h).trans (TateCoordinates.Construction.tateTorsionCoordinates q b hdiv h).symm

/-- A raw coset determines a subgroup of the original torsion group.
The target subtype records only its unmarked elementary group type. -/
def rawBlockTateSubgroupChoicesEquiv (a : Fin 3 → ℕ)
    (ha : ∀ i, a i ≤ h) (hdominant : Antitone a) (h_ElementaryDivisors : ElementaryDivisors.Construction.ElementaryDivisorsInput) :
    Hecke.Construction.rawRightCosetSupport (BlockLatticeCosets.Construction.blockIntegralLevel q) (BlockHeckeChoices.Construction.blockDiagonal q (fun i => (a i : ℤ))) ≃
      {F : AddSubgroup (TateComparison.Add.Tate.torsion q H h) // Nonempty (F ≃+ (∀ i, ZMod (q ^ a i)))} :=
  (BlockHeckeChoices.Construction.rawBlockSubgroupChoicesEquiv q h a ha hdominant h_ElementaryDivisors).trans
    (typedAdditiveSubgroupEquiv (standardBoundedLatticeTorsionEquiv q b hdiv h))

theorem standardBoundedLatticeTorsionEquiv_coordinates
    (x : TateComparison.Add.Tate.Module (H := H) q) :
    standardBoundedLatticeTorsionEquiv q b hdiv h
      ((standardBoundedLatticeResidues q h).symm (IsogenyQuotient.Basis.Construction.basisCoordinateResidues q b (fun _ => h) x)) =
        TateComparison.Evaluation.Tate.evaluate q h x := by
  change (TateCoordinates.Construction.tateTorsionCoordinates q b hdiv h).symm
    (standardBoundedLatticeResidues q h
      ((standardBoundedLatticeResidues q h).symm _)) = _
  rw [AddEquiv.apply_symm_apply, ← TateCoordinates.Construction.tateTorsionCoordinates_evaluate q b hdiv h x, AddEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateChoices.Construction
