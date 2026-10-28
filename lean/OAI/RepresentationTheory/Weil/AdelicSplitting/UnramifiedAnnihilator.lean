import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalMixing
import OAI.RepresentationTheory.Weil.AdelicSplitting.CompactCharacter
import OAI.RepresentationTheory.Weil.AdelicSplitting.BaseChange
import OAI.RepresentationTheory.Weil.AdelicSplitting.UnramifiedCharacter

/-! # Unramified Annihilator -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.UnramifiedAnnihilator.Construction

noncomputable section

/-! The supplied unramified local unitary splittings force the standard
integral lattice to have exactly the prescribed character annihilator at
almost every finite place. -/

open Filter
open scoped _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.CompactCharacter.LocalAnalysis

local instance e26AnnihilatorMeasurable (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel (v.adicCompletion F)
local instance e26AnnihilatorBorel (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem normalized_local_annihilator_integer
    (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (hds : ¬ IsSquare d)
    (n m : ℕ) (hN : 0 < n * m)
    (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
    (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P) :
    ∀ᶠ v in cofinite, ∀ u : ArchimedeanAdeles.Construction.Completion F v,
      (∀ t ∈ Integral.Construction.localIntegerRing F v, Characters.Construction.localAdditiveCharacter F C.ψ v (u * t) = 1) →
        u ∈ Integral.Construction.localIntegerRing F v := by
  obtain ⟨g, i, j, ha⟩ := RationalMixing.Construction.exists_rational_unitary_mixing d hds n m hN H K hH hK P.rational
  let a : F := (TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational g).val (.inl i) (.inr j)
  have hi := Integral.Construction.rationalScalar_integral F a⁻¹
  have hg := Integral.Construction.rationalPairLocal_integral F H.val K.val g
  filter_upwards [hi, hg, D.unramified] with v hiv hgv hDv
  intro u hu
  cases v with
  | inl v => exact Subring.mem_top _
  | inr v =>
      let T := D.atPlace (.inr v) (Integral.Construction.rationalPairLocal F H.val K.val (.inr v) g)
      have hT : T.val.2 (Vacuum.Construction.finiteVacuum F (n * m) v) = Vacuum.Construction.finiteVacuum F (n * m) v := (hDv hgv).2
      have hmix := CompactCharacter.LocalAnalysis.vacuum_fixed_oscillator_mixing
        (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
        (Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inr v))
        (Integral.Construction.localIntegerRing F (.inr v)) (Vacuum.Construction.finiteVacuum F (n * m) v) rfl T hT i j u hu
      change (Vacuum.Construction.projectionAt F (n * m) C.ψ (.inr v) T).val (.inl i) (.inr j) * u ∈
        Integral.Construction.localIntegerRing F (.inr v) at hmix
      rw [show Vacuum.Construction.projectionAt F (n * m) C.ψ (.inr v) T =
        Assembly.Construction.localDualAction F d n m H K P (.inr v) (Integral.Construction.rationalPairLocal F H.val K.val (.inr v) g)
          from D.covers _ _, BaseChange.Construction.localDualAction_rational] at hmix
      change ArchimedeanAdeles.Construction.rationalScalar F (.inr v) a * u ∈ Integral.Construction.localIntegerRing F (.inr v) at hmix
      have h := (Integral.Construction.localIntegerRing F (.inr v)).mul_mem hiv hmix
      have he : ArchimedeanAdeles.Construction.rationalScalar F (.inr v) a⁻¹ * (ArchimedeanAdeles.Construction.rationalScalar F (.inr v) a * u) = u := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
      rwa [he] at h

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.UnramifiedAnnihilator.Construction
