import OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
import OAI.RepresentationTheory.Theta.Adelic.SplitComparison
import OAI.RepresentationTheory.Theta.Adelic.PolarizationLift

/-! # Split Coordinates -/

namespace OAI.RepresentationTheory.Theta.Adelic.SplitCoordinates

noncomputable section

/-! The split-place formula in a stable standard/dual polarization. The
coordinate data concern quadratic algebras and symplectic matrices only;
the equality of Schwartz operators is a proved conclusion. -/

open scoped _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

local instance (F : Type) [Field F] [NumberField F] (v : FiniteSchwartz.FinitePlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance (F : Type) [Field F] [NumberField F] (v : FiniteSchwartz.FinitePlace F) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (F : Type) [Field F] [NumberField F] (d : F)
    (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K) (v : FiniteSchwartz.FinitePlace F)

/-- A split place and coordinates on a stable standard/dual polarization.
The coordinate condition identifies the actual tensor symplectic matrices,
and contains no statement about metaplectic lifts or their scalar factors. -/
structure StableSplitCoordinates where
  root : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)
  root_sq : root ^ 2 = Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d
  identify : Matrix.SpecialLinearGroup (Fin 3) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) ≃*
    SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v))
  symplectic_matrix : ∀ g,
    Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 1 H K P (.inr v)
        (FiniteSchwartz.localSUToPair F H K (.inr v) (identify g)) =
      Weil.Local.Generators.Construction.leviSymplectic (Matrix.SpecialLinearGroup.toGL g)

/-- Stable coordinates allowing a change from the given global rational
polarization. No compatibility with that rational polarization is assumed
for the new local standard/dual decomposition. -/
structure SplitPolarization where
  root : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)
  root_sq : root ^ 2 = Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d
  identify : Matrix.SpecialLinearGroup (Fin 3) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) ≃*
    SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v))
  change : Weil.Local.FunctionsMetaplectic.Construction.Symplectic (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) 3
  symplectic_matrix : ∀ g,
    change * Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 1 H K P (.inr v)
        (FiniteSchwartz.localSUToPair F H K (.inr v) (identify g)) * change⁻¹ =
      Weil.Local.Generators.Construction.leviSymplectic (Matrix.SpecialLinearGroup.toGL g)

variable (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 1)
    (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 1 H K hd C P)

theorem local_split_substitution (B : StableSplitCoordinates F d H K P v)
    (g : Matrix.SpecialLinearGroup (Fin 3) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)))
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) 3) (x : Weil.Local.FunctionsMetaplectic.Construction.Position (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) 3) :
    (FiniteSchwartz.localSUAction F H K hd C P D v (B.identify g) f).val x =
      f.val ((g⁻¹).val.mulVec x) := by
  let : MeasurableSpace (v.adicCompletion F) := borel _
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : CharZero (v.adicCompletion F) := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inr v)
  let : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  have hk : ¬ DiscreteTopology (v.adicCompletion F) := by
    intro h
    let : DiscreteTopology (v.adicCompletion F) := h
    exact not_isOpen_singleton (0 : v.adicCompletion F) (isOpen_discrete _)
  let s := (FiniteSchwartz.localSUSplitting F H K hd C P D (.inr v)).toMonoidHom.comp B.identify.toMonoidHom
  have hp (a : Matrix.SpecialLinearGroup (Fin 3) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))) :
      Weil.AdelicSplitting.Oscillator.Construction.localProjection (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) 3 (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
        (s a) = Weil.Local.Generators.Construction.leviSymplectic (Matrix.SpecialLinearGroup.toGL a) :=
    (D.covers (.inr v) _).trans (B.symplectic_matrix a)
  exact SplitComparison.sl3_substitution
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous (.inr v))
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inr v)) hk
    (Weil.AdelicSplitting.NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd 3 1 (by decide) H K C P D (.inr v))
    s hp g f x

theorem split_polarization_substitution (B : SplitPolarization F d H K P v) :
    ∃ w : Weil.AdelicSplitting.Vacuum.Construction.CoverAt F 3 C.ψ (.inr v),
      Weil.AdelicSplitting.Vacuum.Construction.projectionAt F 3 C.ψ (.inr v) w = B.change ∧
      ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)))
        (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) 3) (x : Weil.Local.FunctionsMetaplectic.Construction.Position (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) 3),
        (Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) 3 (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
          (w * FiniteSchwartz.localSUSplitting F H K hd C P D (.inr v) (B.identify g) * w⁻¹) f).val x =
            f.val ((g⁻¹).val.mulVec x) := by
  let : MeasurableSpace (v.adicCompletion F) := borel _
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : CharZero (v.adicCompletion F) := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inr v)
  let : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  have hk : ¬ DiscreteTopology (v.adicCompletion F) := by
    intro h
    let : DiscreteTopology (v.adicCompletion F) := h
    exact not_isOpen_singleton (0 : v.adicCompletion F) (isOpen_discrete _)
  have hn := Weil.AdelicSplitting.NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd 3 1 (by decide) H K C P D (.inr v)
  have hc := Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous (.inr v)
  have hu := Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inr v)
  obtain ⟨w, hw⟩ := PolarizationLift.localProjection_surjective
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)) hc hu hk hn 3 B.change
  refine ⟨w, hw, ?_⟩
  let s := (MulAut.conj w).toMonoidHom.comp
    ((FiniteSchwartz.localSUSplitting F H K hd C P D (.inr v)).toMonoidHom.comp B.identify.toMonoidHom)
  have hp (g : Matrix.SpecialLinearGroup (Fin 3) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))) :
      Weil.AdelicSplitting.Oscillator.Construction.localProjection (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) 3 (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
        (s g) = Weil.Local.Generators.Construction.leviSymplectic (Matrix.SpecialLinearGroup.toGL g) := by
    change Weil.AdelicSplitting.Oscillator.Construction.localProjection _ _ _ (w * FiniteSchwartz.localSUSplitting F H K hd C P D (.inr v) (B.identify g) * w⁻¹) = _
    rw [map_mul, map_mul, map_inv, hw]
    exact congrArg (fun a => B.change * a * B.change⁻¹) (D.covers (.inr v) _) |>.trans
      (B.symplectic_matrix g)
  exact SplitComparison.sl3_substitution
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)) hc hu hk hn s hp

end

end OAI.RepresentationTheory.Theta.Adelic.SplitCoordinates
