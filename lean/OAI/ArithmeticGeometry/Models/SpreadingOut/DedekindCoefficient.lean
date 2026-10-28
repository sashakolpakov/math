import OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteTypeCoefficientBase
import Mathlib.RingTheory.DedekindDomain.Dvr

/-! # Dedekind Coefficient -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.DedekindCoefficient.Construction

noncomputable section

/-! A finite coefficient base is dominated by a finite type Dedekind base
with the same generic number field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

structure DedekindCoefficientBase (K : Type u) [Field K] [NumberField K] (s : Finset K) where
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra (𝓞 K) carrier]
  [dedekind : IsDedekindDomain carrier]
  [finiteType : Algebra.FiniteType (𝓞 K) carrier]
  genericMap : carrier →ₐ[𝓞 K] K
  injective : Function.Injective genericMap
  baseMap : Spec (.of carrier) ⟶ CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s
  generic_comp : Spec.map (CommRingCat.ofHom genericMap.toRingHom) ≫ baseMap =
    CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s

attribute [instance] DedekindCoefficientBase.commRing DedekindCoefficientBase.algebra
  DedekindCoefficientBase.dedekind DedekindCoefficientBase.finiteType

theorem coefficient_has_dedekind_base
    {K : Type u} [Field K] [NumberField K] (s : Finset K) :
    Nonempty (DedekindCoefficientBase K s) := by
  let A := CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s
  obtain ⟨d, _, hpow, hle⟩ := Fg.Construction.fg_subalgebra_le_localization A ⟨s, rfl⟩
  let R := Localization.subalgebra.ofField K (Submonoid.powers d) hpow
  have : IsDedekindDomain R := IsLocalization.isDedekindDomain (𝓞 K) hpow R
  have : Algebra.FinitePresentation (𝓞 K) R := IsLocalization.Away.finitePresentation d
  let ψ : A →ₐ[𝓞 K] R := Subalgebra.inclusion hle
  refine ⟨{
    carrier := R
    genericMap := R.val
    injective := Subtype.val_injective
    baseMap := Spec.map (CommRingCat.ofHom ψ.toRingHom)
    generic_comp := ?_ }⟩
  rw [← Spec.map_comp]
  rfl

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.DedekindCoefficient.Construction
