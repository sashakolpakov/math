import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.ArchimedeanDiscrete
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FixedBasis
import OAI.RepresentationTheory.Theta.Geometric.LatticeRestrictionAction

/-! # Rational Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The literal principal SU subgroup is exactly a finite congruence
kernel inside the original full lattice stabilizer. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (N : ℕ)

def Datum.RankThreePELDatum.stableRationalIntegralAction : RepresentationTheory.Theta.Geometric.StableCMArithmetic.stableUnitarySubgroup P.lattice P.b →*
    (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[ℤ] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) where
  toFun g := (Matrix.SpecialLinearGroup.toLin' g.val.val).restrictScalars ℤ
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change Matrix.SpecialLinearGroup.toLin' (1 : Matrix.SpecialLinearGroup (Fin 3) E) x = x
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    change Matrix.SpecialLinearGroup.toLin' (g.val.val * h.val.val) x =
      Matrix.SpecialLinearGroup.toLin' g.val.val (Matrix.SpecialLinearGroup.toLin' h.val.val x)
    rw [map_mul, LinearEquiv.mul_apply]

theorem Datum.RankThreePELDatum.stableRationalIntegralAction_preserves (g : RepresentationTheory.Theta.Geometric.StableCMArithmetic.stableUnitarySubgroup P.lattice P.b)
    (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : P.stableRationalIntegralAction g x ∈ P.lattice.toAddSubgroup ↔ x ∈ P.lattice.toAddSubgroup :=
  g.property x

def Datum.RankThreePELDatum.stableRationalLatticeAction : RepresentationTheory.Theta.Geometric.StableCMArithmetic.stableUnitarySubgroup P.lattice P.b →*
    (P.lattice.toAddSubgroup ≃ₗ[ℤ] P.lattice.toAddSubgroup) :=
  RepresentationTheory.Theta.Geometric.LatticeRestrictionAction.latticeRestrictionAction P.stableRationalIntegralAction P.lattice.toAddSubgroup P.stableRationalIntegralAction_preserves

theorem Datum.RankThreePELDatum.principalRationalMatrix_range_iff (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    g ∈ (P.principalRationalMatrixHom N).range ↔
      (∀ x, Matrix.SpecialLinearGroup.toLin' g.val x ∈ P.lattice ↔ x ∈ P.lattice) ∧
      ∀ x ∈ P.lattice, ∃ y ∈ P.lattice, Matrix.SpecialLinearGroup.toLin' g.val x - x = N • y := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [show Matrix.SpecialLinearGroup.toLin' (P.principalRationalMatrixHom N g).val = g.val from
      P.principalRationalMatrix_linear N g]
    exact ⟨fun x => (g.property.1.1 x).symm, g.property.1.2⟩
  · rintro ⟨hL, hN⟩
    let f := Matrix.SpecialLinearGroup.toLin' g.val
    have hd : LinearMap.det f.toLinearMap = 1 := by
      rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap, ← LinearMap.det_toMatrix', LinearMap.toMatrix'_toLin']
      exact g.val.property
    have hf : f ∈ Groups.principalSpecialUnitary P.b P.lattice N := by
      refine ⟨⟨fun x => (hL x).symm, hN⟩, ?_, ?_⟩
      · exact g.property
      · apply Units.ext
        simpa only [LinearEquiv.coe_det, Units.val_one] using hd
    refine ⟨⟨f, hf⟩, ?_⟩
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.toLin'_injective
    exact P.principalRationalMatrix_linear N ⟨f, hf⟩

theorem Datum.RankThreePELDatum.principalRationalMatrix_le_stable :
    (P.principalRationalMatrixHom N).range ≤ RepresentationTheory.Theta.Geometric.StableCMArithmetic.stableUnitarySubgroup P.lattice P.b :=
  fun g hg => ((P.principalRationalMatrix_range_iff N g).mp hg).1

theorem Datum.RankThreePELDatum.principalRational_modN_kernel :
    (RepresentationTheory.Theta.Geometric.Finite.LatticeCongruence.latticeModNAction N P.stableRationalLatticeAction).ker =
      (P.principalRationalMatrixHom N).range.subgroupOf (RepresentationTheory.Theta.Geometric.StableCMArithmetic.stableUnitarySubgroup P.lattice P.b) := by
  ext g
  rw [Datum.RankThreePELDatum.stableRationalLatticeAction, RepresentationTheory.Theta.Geometric.LatticeRestrictionAction.latticeRestrictionAction_congruence]
  change (∀ x ∈ P.lattice, ∃ y ∈ P.lattice,
      Matrix.SpecialLinearGroup.toLin' g.val.val x - x = N • y) ↔ g.val ∈ (P.principalRationalMatrixHom N).range
  rw [P.principalRationalMatrix_range_iff]
  exact ⟨fun h => ⟨g.property, h⟩, fun h => h.2⟩

theorem Datum.RankThreePELDatum.principalRational_finiteRelIndex (hP : P.IsAdmissible) (hN : N ≠ 0) :
    (P.principalRationalMatrixHom N).range.IsFiniteRelIndex (RepresentationTheory.Theta.Geometric.StableCMArithmetic.stableUnitarySubgroup P.lattice P.b) := by
  let : Module.Finite ℤ P.lattice := Module.Finite.of_basis (P.referenceBasis hP)
  let : AddGroup.FG P.lattice.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp inferInstance
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, ← P.principalRational_modN_kernel]
  exact RepresentationTheory.Theta.Geometric.Finite.LatticeCongruence.latticeModNAction_finiteIndex N hN _

theorem Datum.RankThreePELDatum.principalRational_commensurable (hP : P.IsAdmissible) (hN : N ≠ 0) :
    (P.principalRationalMatrixHom N).range.Commensurable (RepresentationTheory.Theta.Geometric.StableCMArithmetic.stableUnitarySubgroup P.lattice P.b) := by
  refine ⟨P.principalRational_finiteRelIndex N hP hN, ⟨?_⟩⟩
  rw [Subgroup.relIndex_eq_one.mpr (P.principalRationalMatrix_le_stable N)]
  exact one_ne_zero

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
