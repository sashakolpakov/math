import OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
import OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizedRationalFamilies

/-! # Rational SU -/

namespace OAI.RepresentationTheory.Theta.Adelic.RationalSU

noncomputable section

/-! Actual rational, archimedean, and finite special-unitary embeddings.
Their product is the existing rational adelic dual-pair embedding. -/

open scoped _root_.NumberField
open Filter

open OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizedRationalFamilies.Construction
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (F : Type) [Field F] [NumberField F] {n m : ℕ} {d : F}
variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

def rationalLocalSU (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) : SpecialUnitary.SU H.val →* SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val v) where
  toFun g :=
    ⟨(Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F H.val v (SpecialUnitary.includeUnitary H.val g)).val,
      (Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F H.val v (SpecialUnitary.includeUnitary H.val g)).property, by
        apply Units.ext
        change ((Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v).mapMatrix g.val.val).det = 1
        rw [← RingHom.map_det]
        have hg : g.val.val.det = 1 := congrArg Units.val g.property.2
        rw [hg, map_one]⟩
  map_one' := by
    apply Subtype.ext
    change (Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F H.val v (SpecialUnitary.includeUnitary H.val 1)).val = 1
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    change (Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F H.val v (SpecialUnitary.includeUnitary H.val (g * h))).val =
      (Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F H.val v (SpecialUnitary.includeUnitary H.val g)).val *
        (Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F H.val v (SpecialUnitary.includeUnitary H.val h)).val
    rw [map_mul, map_mul]
    rfl

theorem rationalLocalSU_include (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (g : SpecialUnitary.SU H.val) :
    SpecialUnitary.includeUnitary (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val v) (rationalLocalSU F H v g) =
      Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F H.val v (SpecialUnitary.includeUnitary H.val g) := rfl

theorem rationalLocalSU_integral (g : SpecialUnitary.SU H.val) :
    ∀ᶠ v in cofinite, rationalLocalSU F H v g ∈ IntegralTopology.localSUIntegral F H.val v :=
  Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal_integral F H.val (SpecialUnitary.includeUnitary H.val g)

def rationalFiniteSU : SpecialUnitary.SU H.val →* FiniteSchwartz.FiniteSU F H :=
  Weil.AdelicSplitting.RestrictedLimits.Construction.diagonalMap (fun v : FiniteSchwartz.FinitePlace F => IntegralTopology.localSUIntegral F H.val (.inr v))
    (fun v => rationalLocalSU F H (.inr v))
    (fun g => Sum.inr_injective.tendsto_cofinite.eventually (rationalLocalSU_integral F H g))

abbrev ArchimedeanSU :=
  ∀ v : NumberField.InfinitePlace F, SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl v))

def rationalArchimedeanSU : SpecialUnitary.SU H.val →* ArchimedeanSU F H :=
  MonoidHom.pi (fun v => rationalLocalSU F H (.inl v))

def adelicSUPair : (ArchimedeanSU F H × FiniteSchwartz.FiniteSU F H) →* Weil.AdelicSplitting.Integral.Construction.AdelicDualPair F H.val K.val where
  toFun g :=
    ⟨fun v => match v with
      | .inl w => (SpecialUnitary.includeUnitary _ (g.1 w), 1)
      | .inr w => (SpecialUnitary.includeUnitary _ (g.2 w), 1), by
        have hfin : ∀ᶠ v : FiniteSchwartz.FinitePlace F in cofinite,
            (SpecialUnitary.includeUnitary _ (g.2 v), (1 : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val (.inr v))) ∈
              Weil.AdelicSplitting.Integral.Construction.localPairIntegral F H.val K.val (.inr v) := by
          filter_upwards [g.2.property] with v hv
          exact ⟨hv, (Weil.AdelicSplitting.Integral.Construction.localUnitaryIntegral F K.val (.inr v)).one_mem⟩
        have htail := Weil.AdelicSplitting.UnramifiedCharacter.Construction.eventually_cofinite_sum_right (I := NumberField.InfinitePlace F) _ hfin
        have harch : ∀ᶠ v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F in cofinite,
            v ∉ Set.range (Sum.inl : NumberField.InfinitePlace F → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :=
          (Set.finite_range (Sum.inl : NumberField.InfinitePlace F → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)).compl_mem_cofinite
        filter_upwards [htail, harch] with v ht hv
        cases v with
        | inl v => exact (hv ⟨v, rfl⟩).elim
        | inr v => exact ht⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro v
    cases v <;> rfl
  map_mul' g h := by
    apply RestrictedProduct.ext
    intro v
    cases v with
    | inl v =>
        change (SpecialUnitary.includeUnitary _ (g.1 v * h.1 v), (1 : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val (.inl v))) =
          (SpecialUnitary.includeUnitary _ (g.1 v) * SpecialUnitary.includeUnitary _ (h.1 v), 1 * 1)
        rw [map_mul, one_mul]
    | inr v =>
        change (SpecialUnitary.includeUnitary _ (g.2 v * h.2 v), (1 : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val (.inr v))) =
          (SpecialUnitary.includeUnitary _ (g.2 v) * SpecialUnitary.includeUnitary _ (h.2 v), 1 * 1)
        rw [map_mul, one_mul]

theorem rational_adelicSUPair (g : SpecialUnitary.SU H.val) :
    adelicSUPair F H K (rationalArchimedeanSU F H g, rationalFiniteSU F H g) =
      Weil.AdelicSplitting.Integral.Construction.rationalPair F H.val K.val (SpecialUnitary.includeUnitary H.val g, 1) := by
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inl v =>
      change (_, 1) = (Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F H.val (.inl v) (SpecialUnitary.includeUnitary H.val g),
        Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F K.val (.inl v) 1)
      rw [map_one]
      rfl
  | inr v =>
      change (_, 1) = (Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F H.val (.inr v) (SpecialUnitary.includeUnitary H.val g),
        Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F K.val (.inr v) 1)
      rw [map_one]
      rfl

variable (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

def specialUnitaryLift : (ArchimedeanSU F H × FiniteSchwartz.FiniteSU F H) →* Weil.AdelicSplitting.Vacuum.Construction.GlobalCover F (n * m) C.ψ :=
  (Weil.AdelicSplitting.Assembly.Construction.constructedAdelicLift F d n m H K hd C P D).toMonoidHom.comp (adelicSUPair F H K)

theorem specialUnitaryLift_rational (g : SpecialUnitary.SU H.val) :
    specialUnitaryLift F H K hd C P D (rationalArchimedeanSU F H g, rationalFiniteSU F H g) =
      Weil.AdelicSplitting.Assembly.Construction.constructedAdelicLift F d n m H K hd C P D
        (Weil.AdelicSplitting.Integral.Construction.rationalPair F H.val K.val (SpecialUnitary.includeUnitary H.val g, 1)) :=
  congrArg (Weil.AdelicSplitting.Assembly.Construction.constructedAdelicLift F d n m H K hd C P D) (rational_adelicSUPair F H K g)

end

end OAI.RepresentationTheory.Theta.Adelic.RationalSU
