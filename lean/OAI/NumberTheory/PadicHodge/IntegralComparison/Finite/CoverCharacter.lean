import OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacter
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverFiniteness

/-! # Cover Character -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverCharacter

noncomputable section

/-! An additive, choice-independent overlap character for actual finite
coefficient H¹ on a connected cover that kills H¹. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Abelian

universe u
variable (ℓ n : ℕ) [Fact ℓ.Prime] {X : Scheme.{u}}

theorem coefficient_restrictions_eq {U D : X.ProEt} [PreconnectedSpace U.left]
    (a b : D ⟶ U) (s : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.obj (op U)) :
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.map a.op s =
      (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.map b.op s := by
  change ULift.{u + 1} C(U.left, ZMod (ℓ ^ n)) at s
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  exact TotallyDisconnectedSpace.eq_of_continuous s.down s.down.continuous (a.left x) (b.left x)

abbrev presentation (X : Scheme.{u}) : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  ShortComplex.mk _ _ (cokernel.condition (Injective.ι (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X)))

omit [Fact (Nat.Prime ℓ)] in
theorem presentation_shortExact : (presentation ℓ n X).ShortExact :=
  { exact := ShortComplex.exact_of_g_is_cokernel _
      (cokernelIsCokernel (presentation ℓ n X).f) }

variable (U D : X.ProEt) (a b : D ⟶ U) [PreconnectedSpace U.left]
  (hzero : ∀ x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H 1,
    AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n U.hom 1 x = 0)

def character : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H 1 →+
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.obj (op D) :=
  IntegralComparison.CoverCharacter.character (presentation ℓ n X) (presentation_shortExact ℓ n) U D a b
    (CoverFiniteness.presentation_local_lifts ℓ n
      (presentation ℓ n X).X₂ (presentation ℓ n X).X₃
      (presentation ℓ n X).f (presentation ℓ n X).g (presentation ℓ n X).zero
      (presentation_shortExact ℓ n) U hzero)
    (coefficient_restrictions_eq ℓ n a b)

variable [Surjective (terminal.from U).left] [QuasiCompact (terminal.from U).left]

theorem character_injective
    (hD : IsPullback a.left b.left (terminal.from U).left (terminal.from U).left) :
    Function.Injective (character ℓ n U D a b hzero) :=
  IntegralComparison.CoverCharacter.character_injective (presentation ℓ n X) (presentation_shortExact ℓ n)
    U D a b _ (coefficient_restrictions_eq ℓ n a b) hD

omit [Surjective (terminal.from U).left] [QuasiCompact (terminal.from U).left] in
theorem character_cocycle (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H 1)
    (T : X.ProEt) (p q r : T ⟶ D)
    (hpa : p ≫ a = r ≫ a) (hpb : p ≫ b = q ≫ a) (hqb : q ≫ b = r ≫ b) :
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.map p.op (character ℓ n U D a b hzero x) +
      (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.map q.op (character ℓ n U D a b hzero x) =
        (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.map r.op (character ℓ n U D a b hzero x) :=
  IntegralComparison.CoverCharacter.character_cocycle (presentation ℓ n X) (presentation_shortExact ℓ n)
    U D a b _ (coefficient_restrictions_eq ℓ n a b) x T p q r hpa hpb hqb

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverCharacter
