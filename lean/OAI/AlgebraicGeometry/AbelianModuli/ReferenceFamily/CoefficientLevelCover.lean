import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.AbelianModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedComplexFibers
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.ComplexCover

/-! # Coefficient Level Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientLevelCover

noncomputable section

/-! Every full-level parameter covers the constructed connected
rational coefficient family. A complex fiber is built from the retained
embedding, and its native torsion propagates by the clopen image theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.ComplexCover.LevelCover

variable {k : Type} [Field k] [CharZero k]

def rationalCoefficientBaseMap (s : Finset k) : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase ℚ k s ⟶ Spec (.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing ℚ k s)))

instance rationalCoefficientBaseMap_locallyFiniteType (s : Finset k) :
    LocallyOfFiniteType (rationalCoefficientBaseMap s) := by
  let : Algebra.FiniteType ℚ (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing ℚ k s) := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing_finiteType ℚ k s
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr (inferInstanceAs (Algebra.FiniteType ℚ (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing ℚ k s))))

theorem coefficientBase_has_complex_point (s : Finset k) :
    Nonempty (Foundations.Scheme.ProjectiveSpace.complexBase ⟶ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase ℚ k s) :=
  Level.ComplexCover.nonempty_complex_test (Rat.castHom ℂ) (rationalCoefficientBaseMap s)

variable [IsAlgClosed k] {g n N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (D : Geometric.GroupModel.GeometricGroupModel A.scheme n) [NeZero N]

theorem coefficient_fullFrame_surjective :
    Surjective (Frame.Locus.LevelCover.fullFrameScheme (Geometric.GroupModel.GeometricGroupModel.abelian A D)
      (rationalCoefficientBaseMap D.data.toModel.coefficients) (N := N)).hom := by
  let U := Geometric.GroupModel.GeometricGroupModel.abelian A D
  obtain ⟨q⟩ := coefficientBase_has_complex_point D.data.toModel.coefficients
  let P := @EmbeddedComplexFibers.embeddedComplexFiberProjectivePresentation
    (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing ℚ k D.data.toModel.coefficients) inferInstance g U n
    D.data.embedding D.data.closedImmersion q
  exact Level.CoverIs.LevelCover.fullFrame_surjective_of_complex_fiber U
    (rationalCoefficientBaseMap D.data.toModel.coefficients) q P

theorem geometric_fullFrame_surjective_of_model :
    Surjective (Frame.Locus.LevelCover.fullFrameScheme A
      (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ k D.data.toModel.coefficients ≫
        rationalCoefficientBaseMap D.data.toModel.coefficients) (N := N)).hom := by
  let U := Geometric.GroupModel.GeometricGroupModel.abelian A D
  let p := rationalCoefficientBaseMap D.data.toModel.coefficients
  let t := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ k D.data.toModel.coefficients
  let : Surjective (Frame.Locus.LevelCover.fullFrameScheme U p (N := N)).hom := coefficient_fullFrame_surjective A D
  let : Surjective (Frame.Locus.LevelCover.fullFrameScheme (U.pullback t) (t ≫ p) (N := N)).hom :=
    Level.ComplexCover.LevelCover.fullFrame_surjective_pullback U p t
  let e := Geometric.GroupModel.GeometricGroupModel.fiberIso A D
  let : IsMonHom e.hom := Geometric.GroupModel.GeometricGroupModel.fiberIso_isMonHom A D
  exact Level.ComplexCover.LevelCover.fullFrame_surjective_of_iso (U.pullback t) (t ≫ p) A e

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientLevelCover
