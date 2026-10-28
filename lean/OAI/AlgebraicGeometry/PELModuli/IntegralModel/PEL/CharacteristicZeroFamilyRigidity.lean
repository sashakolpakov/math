import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AddedClassifierRigidity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleReduced
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PrimeLevelCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.TwoLevelExistence
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Characteristic Zero Family Rigidity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.CharacteristicZeroFamilyRigidity

noncomputable section

section

/-! Actual prime-frame covers transfer bounded universal-family rigidity
to every reduced integral PEL family, including nonnoetherian tests. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s p N : ℕ} [Fact p.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {V : Over (Spec (.of R))}

theorem pel_family_rigidity_of_bounded_parameter
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO p N V) (hp : IsUnit (p : R))
    (hclass : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (A : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO p N T),
      ∃ f : T ⟶ V, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback f) A))
    (hRigid : ∀ (T : Over (Spec (.of R))) [IsReduced T.left] (f : T ⟶ V)
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (U.forgetAuxiliary.data.polarized.pullback f.left)
        (U.forgetAuxiliary.data.polarized.pullback f.left)),
      e.abelian.hom = 𝟙 (U.forgetAuxiliary.data.polarized.abelian.pullback f.left).scheme)
    (T : Over (Spec (.of R))) [IsReduced T.left] (A : Has.IntegralPELObject P R iotaO N T)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A.data.polarized A.data.polarized) :
    e.abelian.hom = 𝟙 A.data.polarized.abelian.scheme := by
  obtain ⟨S', u, hu, he, hs, ⟨α⟩⟩ := Integral.PrimeLevelCover.IntegralLevelCover.exists_prime_fullLevel_cover
    A.data.polarized.abelian (Integral.TwoLevelExistence.integer_unit_at_stalk_of_base_unit T.hom p hp)
  have : IsFinite u := hu
  have : Etale u := he
  have : Surjective u := hs
  let Y : Over (Spec (.of R)) := Over.mk (u ≫ T.hom)
  let j : Y ⟶ T := Over.homMk u rfl
  have : IsReduced Y.left := Finite.EtaleReduced.finite_etale_isReduced u
  let B : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO p N Y := IntegralAdded.PELId.IntegralAddedPELLevel.ofPrescribed (A.pullback j) α
  have hlocal : (e.pullback u).abelian.hom = 𝟙 (A.data.polarized.abelian.pullback u).scheme :=
    AddedClassifierRigidity.addedPEL_classifier_prescribed_rigidity U B (hclass Y B) (hRigid Y) (e.pullback u)
  apply (Over.pullback u).map_injective
  exact hlocal.trans ((Over.pullback u).map_id A.data.polarized.abelian.scheme).symm

end

/-! A bounded two-level parameter proves prescribed-level rigidity for
every reduced PEL family over the characteristic-zero field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [CharZero K] [Countable K] {s p N : ℕ} [Fact p.Prime]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iotaO : NumberField.RingOfIntegers E →+* K}
    {V : Over (Spec (.of K))} [IsNoetherian V.left] [LocallyOfFiniteType V.hom]

theorem characteristicZero_pel_family_rigidity
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P K iotaO p N V) (hN : 3 ≤ N)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hclass : ∀ (T : Over (Spec (.of K))) [IsReduced T.left]
      (A : IntegralAdded.PELId.IntegralAddedPELLevel P K iotaO p N T),
      ∃ f : T ⟶ V, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback f) A))
    (T : Over (Spec (.of K))) [IsReduced T.left] (A : Has.IntegralPELObject P K iotaO N T)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A.data.polarized A.data.polarized) :
    e.abelian.hom = 𝟙 A.data.polarized.abelian.scheme := by
  apply pel_family_rigidity_of_bounded_parameter U
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) hclass _ T A e
  intro W _ f a
  have : IsReduced (Over.mk f.left).left := inferInstanceAs (IsReduced W.left)
  exact CharacteristicZeroPolarizedRigidity.characteristicZero_polarized_reduced_rigidity V.hom U.forgetAuxiliary.data.polarized
    hN hPresentations (Over.mk f.left) a

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.CharacteristicZeroFamilyRigidity
