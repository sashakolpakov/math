import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ScalarKernels
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Automorphisms

/-! # Powered Kernels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PoweredKernels.Construction

noncomputable section

/-! Finiteness produces a uniform positive power of each selected-side central
moduli automorphism whose actual geometric kernel is a marked scalar kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.NumberField
open scoped _root_.CategoryTheory.MonObj

def sideChosenExponent {s : ℕ} (side : Fin s → Bool) (v : Fin s) : ℕ :=
  if side v then 0 else 1

theorem sideChosenExponent_le_one {s : ℕ} (side : Fin s → Bool) (v : Fin s) :
    sideChosenExponent side v ≤ 1 := by unfold sideChosenExponent; split <;> omega

def sidePowerType {s : ℕ} (side : Fin s → Bool) (n : ℕ) : TateComparison.Local.IntegralType s :=
  Automorphisms.Construction.natCentralType (fun v => sideChosenExponent side v * n) n
    (fun v => by simpa using Nat.mul_le_mul_right n (sideChosenExponent_le_one side v))

@[simp] theorem sidePowerType_multiplierNat {s : ℕ} (side : Fin s → Bool) (n : ℕ) :
    (sidePowerType side n).multiplierNat = n := rfl

theorem sidePowerType_blockExponent {s : ℕ} (side : Fin s → Bool) (n : ℕ)
    (v : Fin s) (w : Bool) :
    ScalarKernels.Construction.centralBlockExponent (sidePowerType side n) (v, w) = if w = side v then n else 0 := by
  cases hw : side v <;> cases w <;>
    simp [ScalarKernels.Construction.centralBlockExponent, sidePowerType, Automorphisms.Construction.natCentralType, CentralRepresentatives.Construction.centralType,
      TateComparison.Local.IntegralType.exponentNat, TateComparison.Local.IntegralType.multiplierNat, sideChosenExponent, hw]

variable {E K : Type} [Field E] [NumberField E] [IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

/-- The marked scalar and its exponent are chosen once for the entire
moduli space. At every geometric point the powered central graph has an
actual polarized marked isogeny with precisely that scalar's full kernel. -/
theorem exists_powered_side_scalar_kernels
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    (hgood : D.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : Interface.Construction.ActionData D)
    (hTateComparison : Interface.Construction.Conclusion D hgeometry hgood hIsogenyQuotient A)
    (hFiniteness : Arithmetic.Construction.PrincipalizationInput E) (side : Fin s → Bool) :
    ∃ (n : ℕ) (β : 𝓞 E), 0 < n ∧ β ≠ 0 ∧
      β * IsCMField.ringOfIntegersComplexConj E β = (q : 𝓞 E) ^ n ∧
      Marking.Construction.levelReduction E D.level β = 1 ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
        (x : D.GeometricPoint b),
        ∃ (y : D.GeometricPoint b)
          (f : TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) (q ^ n)),
          y = x ≫ Automorphisms.Construction.natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison
            (sideChosenExponent side) 1 (sideChosenExponent_le_one side) ^ n ∧
          ∀ z : Over.mk (𝟙 (Spec (.of k))) ⟶ (D.fiberFamily b x).abelian.scheme,
            z ≫ f.isogeny.hom = 1 ↔ z ≫ Scalar.Construction.scalarMap (D.fiberFamily b x) β = 1 := by
  have hlevel : 0 < D.level := lt_of_lt_of_le (by decide : 0 < 3) hgeometry.fullLevel
  obtain ⟨n, β, hn, hb, hnorm, hmark, hlocal⟩ :=
    Generators.Construction.marked_side_generator_local D hgood hlevel hdegree hFiniteness side
  refine ⟨n, β, hn, hb, hnorm, hmark, ?_⟩
  intro k _ _ b x
  have hlocal' (i : Fin s × Bool) : ∃ u : ℤ_[q]ˣ,
      D.localCharacter i β = (q : ℤ_[q]) ^ ScalarKernels.Construction.centralBlockExponent (sidePowerType side n) i * u := by
    rw [sidePowerType_blockExponent]
    exact hlocal i.1 i.2
  obtain ⟨y, f, hy, hker⟩ := ScalarKernels.Construction.central_scalar_geometric_kernel_comparison
    D hgeometry hgood hIsogenyQuotient hTateComparison.flags (sidePowerType side n)
    (fun v => (sideChosenExponent side v * n : ℕ)) (fun _ _ => rfl)
    β hnorm hmark hlocal' b x
  refine ⟨y, f, ?_, hker⟩
  rw [Automorphisms.Construction.natCentralMap_pow]
  simp only [Nat.one_mul]
  exact hy

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PoweredKernels.Construction
