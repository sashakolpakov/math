import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.Cosets
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitHeckeTopology

/-! # Split Hecke Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitHeckeChoices.Construction

noncomputable section

/-!
The actual split GU raw support, with a single shared rational multiplier,
is classified by the chosen rank-three subgroup choices. The multiplier
factor contributes one coset, while the chosen blocks vary independently.
-/

def rawSupportLevelEquiv {G : Type*} [Group G] {U V : Subgroup G}
    (hUV : U = V) (g : G) : Hecke.Construction.rawRightCosetSupport U g ≃ Hecke.Construction.rawRightCosetSupport V g :=
  (Subgroup.quotientEquivOfEq hUV).subtypeEquiv (by
    intro x
    subst V
    induction x using Quotient.inductionOn with
    | h x => exact Iff.rfl)

variable (s q : ℕ) [Fact q.Prime]

def multiplierIntegralLevel : Subgroup ℚ_[q]ˣ :=
  (Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom).range

theorem splitIntegralLevel_product :
    TateComparison.HeckeKernel.integralLevel s q =
      (Subgroup.pi Set.univ (fun _ : Fin s => BlockLatticeCosets.Construction.blockIntegralLevel q)).prod
        (multiplierIntegralLevel q) := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(Subgroup.mem_pi Set.univ).mpr (fun v _ => ⟨a.1 v, rfl⟩), ⟨a.2, rfl⟩⟩
  · rintro ⟨hblocks, ⟨u, hu⟩⟩
    have hb (v : Fin s) : g.1 v ∈ BlockLatticeCosets.Construction.blockIntegralLevel q :=
      ((Subgroup.mem_pi Set.univ).mp hblocks) v (Set.mem_univ v)
    choose a ha using hb
    exact ⟨(a, u), Prod.ext (funext ha) hu⟩

/-- There is one multiplier coset for the entire product of chosen blocks. -/
def splitRawBlockSupportEquiv (t : TateComparison.Local.LocalType s) :
    Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel s q) (TateComparison.HeckeKernel.representative s q t) ≃
      ∀ v : Fin s, Hecke.Construction.rawRightCosetSupport (BlockLatticeCosets.Construction.blockIntegralLevel q) (BlockHeckeChoices.Construction.blockDiagonal q (t.exponent v)) :=
  ((rawSupportLevelEquiv (splitIntegralLevel_product s q) (TateComparison.HeckeKernel.representative s q t)).trans
    (Product.Cosets.Construction.prodRawSupportEquiv
      (Subgroup.pi Set.univ (fun _ : Fin s => BlockLatticeCosets.Construction.blockIntegralLevel q)) (multiplierIntegralLevel q)
      (fun v => BlockHeckeChoices.Construction.blockDiagonal q (t.exponent v)) (TateComparison.HeckeKernel.qUnit q ^ t.multiplier))).trans
    (((Product.Cosets.Construction.piRawSupportEquiv (fun _ : Fin s => BlockLatticeCosets.Construction.blockIntegralLevel q)
      (fun v => BlockHeckeChoices.Construction.blockDiagonal q (t.exponent v))).prodCongr (Equiv.refl _)).trans
        (Equiv.prodUnique _ _))

def naturalIntegralLocalType (h : ℕ) (a : Fin s → Fin 3 → ℕ)
    (hdominant : ∀ v, Antitone (a v)) : TateComparison.Local.LocalType s where
  multiplier := h
  exponent v i := a v i
  dominant v _i _j hij := Int.ofNat_le.mpr (hdominant v hij)

theorem naturalIntegralLocalType_isIntegral (h : ℕ) (a : Fin s → Fin 3 → ℕ)
    (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v)) :
    (naturalIntegralLocalType s h a hdominant).IsIntegral := by
  refine ⟨Int.natCast_nonneg h, fun v i => ⟨Int.natCast_nonneg _, ?_⟩⟩
  exact Int.ofNat_le.mpr (ha v i)

/-- The prescribed raw split double coset has exactly one point for each
tuple of unmarked subgroup choices of the specified rank-three types. -/
def splitRawSubgroupChoicesEquiv (h : ℕ) (a : Fin s → Fin 3 → ℕ)
    (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v)) (h_ElementaryDivisors : ElementaryDivisors.Construction.ElementaryDivisorsInput) :
    Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel s q)
      (TateComparison.HeckeKernel.representative s q (naturalIntegralLocalType s h a hdominant)) ≃
      ∀ v : Fin s, BlockHeckeChoices.Construction.BlockSubgroupChoices q h (a v) :=
  (splitRawBlockSupportEquiv s q (naturalIntegralLocalType s h a hdominant)).trans
    (Equiv.piCongrRight (fun v => BlockHeckeChoices.Construction.rawBlockSubgroupChoicesEquiv q h (a v)
      (ha v) (hdominant v) h_ElementaryDivisors))

/-- The existing raw spherical operator assigns coefficient one to each
subgroup tuple under the constructed bijection. -/
theorem rawIntegralTypeOperator_choice_coefficient (h : ℕ) (a : Fin s → Fin 3 → ℕ)
    (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v)) (h_ElementaryDivisors : ElementaryDivisors.Construction.ElementaryDivisorsInput)
    (H : ∀ v : Fin s, BlockHeckeChoices.Construction.BlockSubgroupChoices q h (a v)) :
    TateComparison.HeckeKernel.kernel (TateComparison.HeckeKernel.integralLevel s q)
      (SplitHeckeTopology.Construction.rawIntegralTypeOperator s q (naturalIntegralLocalType s h a hdominant))
      ((splitRawSubgroupChoicesEquiv s q h a ha hdominant h_ElementaryDivisors).symm H).val = 1 := by
  let x := (splitRawSubgroupChoicesEquiv s q h a ha hdominant h_ElementaryDivisors).symm H
  change TateComparison.HeckeKernel.kernel (TateComparison.HeckeKernel.integralLevel s q) (HeckeKernel.Construction.sphericalHeckeFromKernel _ _ _) x.val = 1
  rw [HeckeKernel.Construction.sphericalHeckeFromKernel_kernel, Hecke.Construction.rawDoubleCosetKernel_apply, ite_eq_left x.property]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitHeckeChoices.Construction
