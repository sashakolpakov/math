import OAI.RepresentationTheory.Weil.AdelicSplitting.Vacuum
import OAI.RepresentationTheory.Weil.Local.Generators

/-! # Rational -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.Rational.Construction

noncomputable section

/-!
The canonical rational normalization is specified independently by the
Schrödinger generators. We construct their graph subgroup, rather than
postulate a rational section. Proving that this subgroup is the graph of a
homomorphism is part of the target statement; no unitary splitting occurs
in its definition.
-/

open scoped _root_.NumberField Classical BigOperators

open OAI.RepresentationTheory.Weil.Local.Generators.Construction

variable (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

abbrev RestrictedCover := RestrictedLimits.Construction.RestrictedGroup (Vacuum.Construction.coverIntegral F N ψ)

def assembleGlobalCover : RestrictedCover F N ψ →* Vacuum.Construction.GlobalCover F N ψ :=
  CentralProduct.Construction.assembleCover (Vacuum.Construction.coverIntegral F N ψ) (Vacuum.Construction.scalarAt F N ψ)

def localizeLinear (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N) (v : ArchimedeanAdeles.Construction.Places F) : Local.FunctionsMetaplectic.Construction.GeneralLinear (ArchimedeanAdeles.Construction.Completion F v) N :=
  Units.map (ArchimedeanAdeles.Construction.rationalScalar F v).mapMatrix.toMonoidHom A

def CoversRational (γ : Local.FunctionsMetaplectic.Construction.Symplectic F N) (a : RestrictedCover F N ψ) : Prop :=
  ∀ v, Vacuum.Construction.projectionAt F N ψ v (a v) = Vacuum.Construction.rationalSymplecticLocal F N v γ

def IsRationalLevi (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N) (a : RestrictedCover F N ψ) : Prop :=
  CoversRational F N ψ (Local.Generators.Construction.leviSymplectic A) a ∧
  ∀ v (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) N),
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v) f).val x =
      ((Real.sqrt (Local.FunctionsMetaplectic.Construction.localModulus (ArchimedeanAdeles.Construction.Completion F v)
        (Local.FunctionsMetaplectic.Construction.determinantUnit (ArchimedeanAdeles.Construction.Completion F v) (localizeLinear F N A v))))⁻¹ : ℂ) *
        Local.FunctionsMetaplectic.Construction.substitutionOperator (localizeLinear F N A v) f.val x

def IsRationalQuadratic (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) (a : RestrictedCover F N ψ) : Prop :=
  CoversRational F N ψ (Local.Generators.Construction.quadraticSymplectic B) a ∧
  ∀ v (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) N),
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v) f).val x =
      Characters.Construction.localAdditiveCharacter F ψ v
        ((∑ i, ∑ j, x i * ArchimedeanAdeles.Construction.rationalScalar F v (B.val i j) * x j) / 2) * f.val x

def IsRationalFourier (a : RestrictedCover F N ψ) : Prop :=
  CoversRational F N ψ (Local.Generators.Construction.weylSymplectic F N) a ∧
  ∀ v (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) N),
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v) f).val x =
      Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F ψ v)
        (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)) f.val x

def rationalGeneratorPairs : Set (Local.FunctionsMetaplectic.Construction.Symplectic F N × Vacuum.Construction.GlobalCover F N ψ) :=
  {z | (∃ A a, IsRationalLevi F N ψ A a ∧
          z = (Local.Generators.Construction.leviSymplectic A, assembleGlobalCover F N ψ a)) ∨
       (∃ B a, IsRationalQuadratic F N ψ B a ∧
          z = (Local.Generators.Construction.quadraticSymplectic B, assembleGlobalCover F N ψ a)) ∨
       (∃ a, IsRationalFourier F N ψ a ∧
          z = (Local.Generators.Construction.weylSymplectic F N, assembleGlobalCover F N ψ a))}

def rationalGraph : Subgroup (Local.FunctionsMetaplectic.Construction.Symplectic F N × Vacuum.Construction.GlobalCover F N ψ) :=
  Subgroup.closure (rationalGeneratorPairs F N ψ)

def rationalProjectionGraph : Subgroup (Local.FunctionsMetaplectic.Construction.Symplectic F N × Vacuum.Construction.GlobalCover F N ψ) where
  carrier := {z | Vacuum.Construction.globalProjection F N ψ z.2 = Vacuum.Construction.rationalSymplectic F N z.1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change Vacuum.Construction.globalProjection F N ψ (a.2 * b.2) = Vacuum.Construction.rationalSymplectic F N (a.1 * b.1)
    rw [map_mul, map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change Vacuum.Construction.globalProjection F N ψ a.2⁻¹ = Vacuum.Construction.rationalSymplectic F N a.1⁻¹
    rw [map_inv, map_inv, ha]

theorem assembled_covers_rational (γ : Local.FunctionsMetaplectic.Construction.Symplectic F N) (a : RestrictedCover F N ψ)
    (ha : CoversRational F N ψ γ a) :
    Vacuum.Construction.globalProjection F N ψ (assembleGlobalCover F N ψ a) = Vacuum.Construction.rationalSymplectic F N γ := by
  apply RestrictedProduct.ext
  intro v
  exact ha v

theorem rationalGraph_covers : rationalGraph F N ψ ≤ rationalProjectionGraph F N ψ := by
  apply (Subgroup.closure_le (rationalProjectionGraph F N ψ)).mpr
  intro z hz
  rcases hz with ⟨A, a, ha, rfl⟩ | ⟨B, a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact assembled_covers_rational F N ψ _ a ha.1
  · exact assembled_covers_rational F N ψ _ a ha.1
  · exact assembled_covers_rational F N ψ _ a ha.1

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.Rational.Construction
