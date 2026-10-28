import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.Transport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HodgeFullness

/-! # Algebraic Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Algebraize the actual integral Hodge transport between reference
fibers, with exact recovery on periods and on the integral CM action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HodgeFullness.IntrinsicLinearMaps

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z w : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {G : Reference.Fiber.ReferenceAnalyticFiber P w}
    {hP : P.IsAdmissible} (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (W : Reference.AlgebraicModel.ReferenceAlgebraicModel G hP)
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b))
    (hw : w.val = P.lineAction g z.val) (hΛ : ∀ v, v ∈ P.lattice ↔ g v ∈ P.lattice)

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceIso : M.abelian.toOver ≅ W.abelian.toOver :=
  Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeIntegralHodgeIso (M.nativeReferenceTransport W g) (M.nativeReferenceTransport_hodge W g hg hw)
    (M.nativeReferenceTransport_inverse_hodge W g hg hw) (M.nativeReferenceTransport_integral W g hΛ)

instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceIso_isMonHom : IsMonHom (M.nativeReferenceIso W g hg hw hΛ).hom :=
  Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeIntegralHodgeIso_isMonHom _ _ _ _

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceIso_periods :
    Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (M.nativeReferenceIso W g hg hw hΛ).hom = (M.nativeReferenceTransport W g).toLinearMap :=
  Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeIntegralHodgeIso_rational _ _ _ _

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceIso_marking (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (M.nativeReferenceIso W g hg hw hΛ).hom (M.nativeReferenceMarking v) =
      W.nativeReferenceMarking (g v) := by
  rw [M.nativeReferenceIso_periods]
  exact M.nativeReferenceTransport_marking W g v

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceTransport_action (a : NumberField.RingOfIntegers E) :
    (M.nativeReferenceTransport W g).toLinearMap.comp
        (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a))) =
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AbelianScheme.TateComparison.End.endSchemeMap W.abelian.toOver (W.functorAction a))).comp
        (M.nativeReferenceTransport W g).toLinearMap := by
  apply LinearMap.ext
  intro v
  obtain ⟨v, rfl⟩ := M.nativeReferenceMarking.surjective v
  change M.nativeReferenceTransport W g
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)) (M.nativeReferenceMarking v)) =
    Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AbelianScheme.TateComparison.End.endSchemeMap W.abelian.toOver (W.functorAction a))
      (M.nativeReferenceTransport W g (M.nativeReferenceMarking v))
  rw [M.nativeReferenceMarking_action, M.nativeReferenceTransport_marking,
    M.nativeReferenceTransport_marking, W.nativeReferenceMarking_action, map_smul]

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceIso_action (a : NumberField.RingOfIntegers E) :
    AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a) ≫ (M.nativeReferenceIso W g hg hw hΛ).hom =
      (M.nativeReferenceIso W g hg hw hΛ).hom ≫ AbelianScheme.TateComparison.End.endSchemeMap W.abelian.toOver (W.functorAction a) :=
  Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeIntegralHodgeIso_intertwines _ _ _ _ _ _ (M.nativeReferenceTransport_action W g a)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
