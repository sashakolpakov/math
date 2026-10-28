import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.SchemeDescentComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.AbelianSchemeDescentComparison

/-! # Pair -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

section

/-! Actual abelian and dual-cover group schemes on one arithmetic base,
with their cartesian covering diagrams and prescribed kernel pairs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) {S : Scheme.{0}} (b : S ⟶ Spec (.of R))

structure IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair where
  abelian : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) ((Over.pullback b).obj Q).left
  dual : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) ((Over.pullback b).obj Q).left
  abelianCover : ((Over.pullback b).obj U.prescribedTotalSpace).left ⟶ abelian.scheme.left
  dualCover : ((Over.pullback b).obj U.prescribedDualTotalSpace).left ⟶ dual.scheme.left
  abelianCartesian : IsPullback ((Over.pullback b).map U.prescribedProjection).left abelianCover
    ((Over.pullback b).map π).left abelian.scheme.hom
  dualCartesian : IsPullback ((Over.pullback b).map U.prescribedDualProjection).left dualCover
    ((Over.pullback b).map π).left dual.scheme.hom
  abelianKernelPair : IsKernelPair abelianCover
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
    ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left
  dualKernelPair : IsKernelPair dualCover
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
    ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left
  abelianComparison : (Relative.ScalarFunctor.relativeScalarFunctor b X).obj U.forgetAuxiliary.data.polarized.abelian.scheme ≅
    (Over.pullback ((Over.pullback b).map π).left).obj abelian.scheme
  abelianComparison_cover : abelianComparison.hom.left ≫
    CategoryTheory.Limits.pullback.fst abelian.scheme.hom ((Over.pullback b).map π).left = abelianCover
  abelianComparison_group : IsMonHom abelianComparison.hom
  dualComparison : (Relative.ScalarFunctor.relativeScalarFunctor b X).obj U.forgetAuxiliary.data.polarized.dual.abelian.scheme ≅
    (Over.pullback ((Over.pullback b).map π).left).obj dual.scheme
  dualComparison_cover : dualComparison.hom.left ≫
    CategoryTheory.Limits.pullback.fst dual.scheme.hom ((Over.pullback b).map π).left = dualCover
  dualComparison_group : IsMonHom dualComparison.hom

end

/-! The actual two family quotient diagrams construct a pair of
abelian schemes with the exact covering group comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left] [Surjective π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribed_abelian_pair_of_quotients (hrigid : U.PrescribedRigid)
    {S : Scheme.{0}} (b : S ⟶ Spec (.of R)) (A C : Over ((Over.pullback b).obj Q).left)
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [Smooth C.hom] [IsProper C.hom] [GeometricallyConnected C.hom]
    (qA : ((Over.pullback b).obj U.prescribedTotalSpace).left ⟶ A.left)
    (qC : ((Over.pullback b).obj U.prescribedDualTotalSpace).left ⟶ C.left)
    (hA : IsPullback ((Over.pullback b).map U.prescribedProjection).left qA
      ((Over.pullback b).map π).left A.hom)
    (hC : IsPullback ((Over.pullback b).map U.prescribedDualProjection).left qC
      ((Over.pullback b).map π).left C.hom)
    (hkA : IsKernelPair qA ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
      ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left)
    (hkC : IsKernelPair qC ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
      ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left) :
    Nonempty (U.PrescribedAbelianPair hU π hk b) := by
  have hu := Specialization.base_change_square b π
  have : Etale ((Over.pullback b).map π).left := MorphismProperty.of_isPullback hu
    (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left := MorphismProperty.of_isPullback hu
    (inferInstanceAs (Surjective π.left))
  have : Etale qA := MorphismProperty.of_isPullback hA (inferInstanceAs (Etale ((Over.pullback b).map π).left))
  have : Surjective qA := MorphismProperty.of_isPullback hA
    (inferInstanceAs (Surjective ((Over.pullback b).map π).left))
  have : Etale qC := MorphismProperty.of_isPullback hC (inferInstanceAs (Etale ((Over.pullback b).map π).left))
  have : Surjective qC := MorphismProperty.of_isPullback hC
    (inferInstanceAs (Surjective ((Over.pullback b).map π).left))
  obtain ⟨Ab, hAb, eA, heA, hgroupA⟩ :=
    U.prescribed_abelian_scheme_descends_with_comparison hU π hk hrigid b A qA hA hkA
  subst A
  obtain ⟨Db, hDb, eC, heC, hgroupC⟩ :=
    U.prescribed_dual_abelian_scheme_descends_with_comparison hU π hk hrigid b C qC hC hkC
  subst C
  simp only [eqToHom_refl, Category.comp_id] at heA heC
  exact ⟨⟨Ab, Db, qA, qC, hA, hC, hkA, hkC, eA, heA, hgroupA, eC, heC, hgroupC⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
