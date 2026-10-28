import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.PeriodDifferential
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Lattice
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice

/-! # Marking -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The original E-cube gives the native rational period marking of
the constructed reference abelian variety, carrying its prescribed
integral lattice exactly onto the native exponential lattice. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP)

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceEmbedding : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian :=
  (show Reference.Fiber.ReferenceTangent s →+ RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian from
    M.periodDifferential.toAddMonoidHom).toRatLinearMap.comp F.periodEmbedding.toRatLinearMap

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceEmbedding_injective : Function.Injective M.nativeReferenceEmbedding :=
  M.periodDifferential.injective.comp F.embedding_injective

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceEmbedding_lattice_iff (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    M.nativeReferenceEmbedding v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian ↔ v ∈ P.lattice := by
  change M.periodDifferential (F.periodEmbedding v) ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian ↔ _
  refine (M.periodDifferential_lattice_iff (F.periodEmbedding v)).trans ?_
  constructor
  · intro hv
    obtain ⟨w, hw, he⟩ := (F.lattice_membership (F.periodEmbedding v)).mp hv
    exact F.embedding_injective he ▸ hw
  · intro hv
    exact (F.lattice_membership _).mpr ⟨v, hv, rfl⟩

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceEmbedding_lattice_image :
    M.nativeReferenceEmbedding '' (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) =
      (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian : Set (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (M.nativeReferenceEmbedding_lattice_iff w).mpr hw
  · intro hv
    have hpre : M.periodDifferential.symm v ∈ F.periodData.periodIntegerLattice := by
      apply (M.periodDifferential_lattice_iff _).mp
      exact (congrArg (fun w : RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian => w ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian)
        (M.periodDifferential.apply_symm_apply v)).mpr hv
    obtain ⟨w, hw, he⟩ := (F.lattice_membership (M.periodDifferential.symm v)).mp hpre
    refine ⟨w, hw, ?_⟩
    exact (congrArg M.periodDifferential he).symm.trans (M.periodDifferential.apply_symm_apply v)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceEmbedding_range : M.nativeReferenceEmbedding.range = Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian := by
  have hspan : Submodule.span ℚ (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤ := by
    rcases hP with ⟨_, _, _, _, _, _, _, _, _, hlat, _⟩
    exact hlat.2.1
  calc
    M.nativeReferenceEmbedding.range = Submodule.map M.nativeReferenceEmbedding ⊤ :=
      (Submodule.map_top M.nativeReferenceEmbedding).symm
    _ = Submodule.map M.nativeReferenceEmbedding (Submodule.span ℚ (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))) :=
      congrArg (Submodule.map M.nativeReferenceEmbedding) hspan.symm
    _ = Submodule.span ℚ (M.nativeReferenceEmbedding '' (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))) :=
      Submodule.map_span M.nativeReferenceEmbedding _
    _ = Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian := congrArg (Submodule.span ℚ) M.nativeReferenceEmbedding_lattice_image

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceMarking : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian :=
  (LinearEquiv.ofInjective M.nativeReferenceEmbedding M.nativeReferenceEmbedding_injective).trans
    (LinearEquiv.ofEq _ _ M.nativeReferenceEmbedding_range)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceMarking_apply (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    (M.nativeReferenceMarking v).val = M.periodDifferential (F.periodEmbedding v) := rfl

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceMarking_integral (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    M.nativeReferenceMarking v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods M.abelian ↔ v ∈ P.lattice :=
  M.nativeReferenceEmbedding_lattice_iff v

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
