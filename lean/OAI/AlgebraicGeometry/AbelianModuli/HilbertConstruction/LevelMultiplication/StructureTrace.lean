import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.FiniteFlatTrace
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.Degree

/-! # Structure Trace -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Full-level multiplication of invertible level admits an actual normalized trace retraction on the structure sheaf of an abelian scheme over a locally Noetherian base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Abelian.Schemes.AbelianScheme.fullLevel_multiplication_structureUnit_splitMono
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N) (hN : IsUnit (N : Γ(S, ⊤))) :
    IsSplitMono (SheafOfModules.unitToPushforwardObjUnit (A.multiplication N).left.toRingCatSheafHom) := by
  have : IsLocallyNoetherian A.scheme.left := LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom
  have := A.fullLevel_multiplication_etale level
  have := A.fullLevel_multiplication_isFinite level
  have hdegree : IsUnit ((N ^ (2 * g) : ℕ) : Γ(A.scheme.left, ⊤)) := by
    simpa only [Nat.cast_pow] using (Abelian.Schemes.level_unit_under_base_change A.scheme.hom N hN).pow (2 * g)
  obtain ⟨u, hu⟩ := hdegree
  exact LocallyNoetherian.FiniteFlatTrace.locallyNoetherianFiniteFlat_structureUnit_splitMono (A.multiplication N).left
    (A.fullLevel_multiplication_finrank level) u hu

theorem Abelian.Schemes.AbelianScheme.fullLevel_multiplication_pullbackStructureUnit_splitMono
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N) (hN : IsUnit (N : Γ(S, ⊤))) :
    IsSplitMono ((Scheme.Modules.pullbackPushforwardAdjunction (A.multiplication N).left).unit.app
      (Line.Bundles.structureModule A.scheme.left)) := by
  have : IsLocallyNoetherian A.scheme.left := LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom
  have := A.fullLevel_multiplication_etale level
  have := A.fullLevel_multiplication_isFinite level
  have hdegree : IsUnit ((N ^ (2 * g) : ℕ) : Γ(A.scheme.left, ⊤)) := by
    simpa only [Nat.cast_pow] using (Abelian.Schemes.level_unit_under_base_change A.scheme.hom N hN).pow (2 * g)
  obtain ⟨u, hu⟩ := hdegree
  exact LocallyNoetherian.FiniteFlatTrace.locallyNoetherianFiniteFlat_pullbackStructureUnit_splitMono (A.multiplication N).left
    (A.fullLevel_multiplication_finrank level) u hu

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
