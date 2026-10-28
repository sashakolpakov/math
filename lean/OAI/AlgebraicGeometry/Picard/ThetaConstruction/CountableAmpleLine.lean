import OAI.AlgebraicGeometry.Picard.ThetaConstruction.CountableProjectiveAbelianModel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.RecoveredLines
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricAmpleNeighborhood
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation

/-! # Countable Ample Line -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.CountableAmpleLine.Geometric

noncomputable section

/-! An actual ample line and its abelian group descend together to
a countable algebraically closed subfield. Ampleness is reflected
from the original line through the actual cartesian field comparison. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.RecoveredLines.Construction

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

structure CountableAmpleLineModel where
  field : Subfield k
  [countable : Countable field]
  [algebraicallyClosed : IsAlgClosed field]
  abelian : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of field))
  recovery : A.scheme ≅ (abelian.pullback (Spec.map (CommRingCat.ofHom field.subtype))).scheme
  recovery_group : IsMonHom recovery.hom
  line : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle abelian.scheme.left
  ample : line.IsAmple
  line_recovery : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
    (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap (Spec.map (CommRingCat.ofHom field.subtype)) A.scheme abelian.scheme recovery)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf line) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L

attribute [instance] CountableAmpleLineModel.countable CountableAmpleLineModel.algebraicallyClosed
  CountableAmpleLineModel.recovery_group

theorem exists_countable_ample_line_model (hL : L.IsAmple) : Nonempty (CountableAmpleLineModel A L) := by
  obtain ⟨F, hF, ha, _, B, e, he⟩ :=
    CountableProjectiveAbelianModel.Geometric.exists_countable_projective_abelian_model A (hL.projectivePresentation A.scheme.hom)
  let : Countable F := hF
  let : IsAlgClosed F := ha
  let : IsMonHom e.hom := he
  obtain ⟨G, hG, hGa, hFG, J, hJ⟩ := AbelianScheme.IsogenyQuotient.Countable.RecoveredLines.Construction.countable_recovered_line_model_exists F B A e L
  let : Countable G := hG
  let : IsAlgClosed G := hGa
  let v := (AbelianScheme.IsogenyQuotient.Countable.ParameterLines.Construction.subfieldParameter F G hFG).hom
  let u := Spec.map (CommRingCat.ofHom G.subtype)
  let w := Spec.map (CommRingCat.ofHom F.subtype)
  let B' : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of G)) := B.pullback v
  let : IsProper B'.scheme.hom := B'.proper
  let e' : A.scheme ≅ (B'.pullback u).scheme :=
    AbelianScheme.IsogenyQuotient.StagedRecovery.Construction.stagedAbelianRecovery B A v u w (AbelianScheme.IsogenyQuotient.Countable.ParameterLines.Construction.subfieldParameterRestriction F G hFG).w e
  let : IsMonHom e'.hom := AbelianScheme.IsogenyQuotient.StagedRecovery.Construction.stagedAbelianRecovery_isMonHom B A v u w
    (AbelianScheme.IsogenyQuotient.Countable.ParameterLines.Construction.subfieldParameterRestriction F G hFG).w e
  let c := AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u A.scheme B'.scheme e'
  let : Surjective u := ⟨Function.surjective_to_subsingleton _⟩
  have hamp : J.IsAmple := PELModuli.IntegralModel.GeometricAmpleNeighborhood.proper_isAmple_of_field_baseChange B'.scheme.hom J
    c A.scheme.hom u (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap_isPullback u A.scheme B'.scheme e').flip
    (hL.of_iso (Quotient.exact hJ).some.symm)
  exact ⟨{
    field := G
    abelian := B'
    recovery := e'
    recovery_group := AbelianScheme.IsogenyQuotient.StagedRecovery.Construction.stagedAbelianRecovery_isMonHom B A v u w
      (AbelianScheme.IsogenyQuotient.Countable.ParameterLines.Construction.subfieldParameterRestriction F G hFG).w e
    line := J
    ample := hamp
    line_recovery := hJ }⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.CountableAmpleLine.Geometric
