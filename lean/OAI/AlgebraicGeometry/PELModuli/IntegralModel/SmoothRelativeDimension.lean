import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CotangentDimension
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties

/-! # Smooth Relative Dimension -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothRelativeDimension.DimensionSupport

noncomputable section

/-! The actual local dimension of smooth charts of fixed relative dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CotangentDimension.Construction

universe u

/-- A standard smooth algebra of relative dimension n over a perfect field
has local dimension n at every maximal ideal. -/
theorem ringKrullDim_localization_maximal_of_standardSmooth
    (K B : Type*) [Field K] [PerfectField K] [CommRing B] [Algebra K B]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n K B]
    (p : Ideal B) [p.IsMaximal] :
    ringKrullDim (Localization.AtPrime p) = (n : WithBot ℕ∞) := by
  have : Nontrivial B := (algebraMap B p.ResidueField).domain_nontrivial
  have : Algebra.IsStandardSmooth K B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  rw [ArithmeticGeometry.OrdinaryLocus.Openness.CotangentDimension.Construction.ringKrullDim_localization_maximal_eq_rankAtStalk_kaehler K B p,
    Module.rankAtStalk_eq_finrank_of_free]
  exact congrArg (fun m : ℕ => (m : WithBot ℕ∞))
    (Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n))

/-- Smooth relative dimension over a perfect field agrees with local
Krull dimension at closed points. -/
theorem ringKrullDim_stalk_of_smoothOfRelativeDimension
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
    (n : ℕ) (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension n f]
    (x : X) (hx : IsClosed {x}) :
    ringKrullDim (X.presheaf.stalk x) = (n : WithBot ℕ∞) := by
  obtain ⟨U, _, V, hV, hxV, hVU, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  have hU : U = ⊤ := by
    apply le_antisymm le_top
    intro y _
    exact (Subsingleton.elim (f x) y) ▸ hVU hxV
  subst U
  let R := Γ(Spec (.of K), ⊤)
  let B := Γ(X, V)
  let e := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  let : Field R := (e.toMulEquiv.isField (Field.toIsField K)).toField
  have : PerfectField R := PerfectField.of_ringEquiv e.symm
  let : Algebra R B := (f.appLE ⊤ V hVU).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n R B := hstd
  let p := hV.primeIdealOf ⟨x, hxV⟩
  have : p.asIdeal.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  have : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  let e' := (IsLocalization.algEquiv p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) (X.presheaf.stalk x)).toRingEquiv
  exact (ringKrullDim_eq_of_ringEquiv e').symm.trans
    (ringKrullDim_localization_maximal_of_standardSmooth R B n p.asIdeal)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothRelativeDimension.DimensionSupport
