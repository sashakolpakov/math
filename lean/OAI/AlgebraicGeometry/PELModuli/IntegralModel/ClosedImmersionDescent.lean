import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.QuotientFactor
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Quasi

/-! # Closed Immersion Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ClosedImmersionDescent

noncomputable section

/-! Closed embeddings descend through faithfully flat scalar extension.
The proof reflects the monomorphism and the local geometric properties,
then uses the proved finite-monomorphism criterion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem closedImmersion_of_fpqc_baseChange {S S' : Scheme}
    (u : S' ⟶ S) [Flat u] [Surjective u] [QuasiCompact u]
    {A B : Over S} (f : A ⟶ B)
    [IsClosedImmersion ((Over.pullback u).map f).left] : IsClosedImmersion f.left := by
  let F := Over.pullback u
  have : Mono (F.map f) := Over.mono_of_mono_left _
  have : Mono f := F.mono_of_mono_map inferInstance
  have : Mono f.left := inferInstance
  have : LocallyOfFiniteType f.left := Arithmetic.QuotientFactor.property_of_fpqc_baseChange u (@LocallyOfFiniteType) f inferInstance
  have : UniversallyClosed f.left := Arithmetic.QuotientFactor.property_of_fpqc_baseChange u (@UniversallyClosed) f inferInstance
  have : FormallyUnramified f.left := Arithmetic.QuotientFactor.property_of_fpqc_baseChange u (@FormallyUnramified) f inferInstance
  have : IsProper f.left := ⟨⟩
  have : IsFinite f.left := AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified f.left
  exact (IsClosedImmersion.iff_isFinite_and_mono f.left).mpr ⟨inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ClosedImmersionDescent
