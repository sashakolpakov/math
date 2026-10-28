import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockCosetLatticeAction

/-! # Split Coset Components -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitCosetComponents

noncomputable section

/-! A split similitude coset records its independent GL3 lattices
and one scalar coset. The scalar factor is retained only once. -/

variable (s q : ℕ) [Fact q.Prime]

def scalarIntegralLevel : Subgroup ℚ_[q]ˣ :=
  (Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom).range

def splitCosetMap : HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q →
    (Fin s → Matrix.GeneralLinearGroup (Fin 3) ℚ_[q] ⧸ IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q) ×
      (ℚ_[q]ˣ ⧸ scalarIntegralLevel q) :=
  Quotient.lift (fun g => ((fun i => QuotientGroup.mk (g.1 i)), QuotientGroup.mk g.2)) (by
    intro g h hrel
    have hr := (CentralConvolution.integralLevel_mem_iff s q (g⁻¹ * h)).mp (QuotientGroup.leftRel_apply.mp hrel)
    apply Prod.ext
    · funext i
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (hr.1 i))
    · exact Quotient.sound (QuotientGroup.leftRel_apply.mpr hr.2))

theorem splitCosetMap_bijective : Function.Bijective (splitCosetMap s q) := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h g =>
      induction y using Quotient.inductionOn with
      | h h =>
        intro he
        apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        apply (CentralConvolution.integralLevel_mem_iff s q (g⁻¹ * h)).mpr
        constructor
        · intro i
          exact QuotientGroup.leftRel_apply.mp (Quotient.exact (congrArg (fun z => z.1 i) he))
        · exact QuotientGroup.leftRel_apply.mp (Quotient.exact (congrArg Prod.snd he))
  · rintro ⟨x, y⟩
    have hx (i : Fin s) : ∃ g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q], QuotientGroup.mk g = x i :=
      Quotient.exists_rep (x i)
    choose g hg using hx
    obtain ⟨a, ha⟩ := Quotient.exists_rep y
    exact ⟨QuotientGroup.mk (g, a), Prod.ext (funext hg) ha⟩

def splitCosetEquiv : HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q ≃
    (Fin s → Matrix.GeneralLinearGroup (Fin 3) ℚ_[q] ⧸ IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q) ×
      (ℚ_[q]ˣ ⧸ scalarIntegralLevel q) :=
  Equiv.ofBijective (splitCosetMap s q) (splitCosetMap_bijective s q)

theorem splitCosetEquiv_mk (g : HeckeKernel.SplitGroup s q) :
    splitCosetEquiv s q (QuotientGroup.mk g) =
      ((fun i => QuotientGroup.mk (g.1 i)), QuotientGroup.mk g.2) := rfl

def splitCosetLatticeEquiv : HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q ≃
    (Fin s → Duality.RankThreeLattice ℤ_[q] ℚ_[q]) × (ℚ_[q]ˣ ⧸ scalarIntegralLevel q) :=
  (splitCosetEquiv s q).trans
    (Equiv.prodCongr (Equiv.piCongrRight (fun _ => IsogenyQuotient.BlockLatticeCosets.Construction.blockLatticeCosetEquiv q)) (Equiv.refl _))

theorem splitCosetLatticeEquiv_mk (g : HeckeKernel.SplitGroup s q) :
    splitCosetLatticeEquiv s q (QuotientGroup.mk g) =
      ((fun i => IsogenyQuotient.BlockLatticeCosets.Construction.matrixBlockLattice q (g.1 i)), QuotientGroup.mk g.2) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitCosetComponents
