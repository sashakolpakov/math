import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ModelsHas
import OAI.ArithmeticGeometry.Models.SpreadingOut.Core

/-! # Spreading Out Capstones -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SpreadingOutCapstones

noncomputable section

/-! Adapters from the completed SpreadingOut capstones to IntegralModel's exact arithmetic
interfaces. The SpreadingOut input proposition is now proved, rather than assumed.
The frozen SpreadingOut statement placeholder is not imported. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def finiteExtensionOfSpreadingOut {K : Type u} [Field K] [NumberField K]
    (L : ArithmeticGeometry.Models.SpreadingOut.FiniteFieldComponents.Construction.FiniteNumberFieldExtension K) : Arithmetic.Open.FiniteNumberFieldExtension K :=
  ⟨L.carrier⟩

def arithmeticOpenOfSpreadingOut {K : Type u} [Field K] [NumberField K]
    (B : ArithmeticGeometry.Models.SpreadingOut.Base.Construction.ArithmeticOpen K) : Arithmetic.Open.ArithmeticOpen K where
  U := B.U
  finite_complement := B.finite_complement
  generic := B.generic
  generic_eq := B.generic_eq

/-- The complete finite-diagram input previously exposed by IntegralModel follows
from SpreadingOut's proved capstone, preserving every map and designated group. -/
theorem provedSpreadingOutInput (K : Type u) [Field K] [NumberField K] : ModelsHas.SpreadingOutInput K := by
  intro D
  obtain ⟨L, B, M, fM, e, groupM, hM, he, hg⟩ :=
    ArithmeticGeometry.Models.SpreadingOut.SpreadFiniteDiagram.Construction.spread_finite_diagram_with_abelian_varieties K D.X
      D.smooth D.proper D.src D.dst D.f D.abelianIndex D.group D.abelian
  exact ⟨{
    extension := finiteExtensionOfSpreadingOut L
    base := arithmeticOpenOfSpreadingOut B
    M := M
    fM := fM
    e := e
    groupM := groupM
    properties := hM
    compatible := he
    abelian := hg }⟩

/-- No field extension is needed for one smooth proper arithmetic model. -/
theorem smooth_proper_arithmetic_model
    (K : Type u) [Field K] [NumberField K] (X : Over (Arithmetic.Open.fieldBase K))
    [Smooth X.hom] [IsProper X.hom] :
    ∃ (B : Arithmetic.Open.ArithmeticOpen K) (M : Over B.U.toScheme),
      Smooth M.hom ∧ IsProper M.hom ∧ Nonempty ((Over.pullback B.generic).obj M ≅ X) := by
  obtain ⟨B, M, hs, hp, he⟩ :=
    ArithmeticGeometry.Models.SpreadingOut.SmoothProperModel.Construction.smooth_proper_model_outside_finitely_many_primes K X
  exact ⟨arithmeticOpenOfSpreadingOut B, M, hs, hp, he⟩

/-- The simultaneous split model and preservation of all originally
surjective arrows are now unconditional geometric constructions. -/
theorem exists_split_surjective_diagram_model
    {K : Type u} [Field K] [NumberField K] (D : ModelsHas.FiniteDiagram K) :
    ∃ M : ModelsHas.DiagramModel D,
      ∀ a : D.arrows, Surjective (D.f a).left → Surjective (M.fM a).left :=
  ModelsHas.spread_surjective_diagram (provedSpreadingOutInput K) D

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SpreadingOutCapstones
