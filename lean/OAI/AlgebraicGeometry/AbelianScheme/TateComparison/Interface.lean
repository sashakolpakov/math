import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricFlags
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Cohomology
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Marking
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Albanese

/-! # Interface -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-!
Concrete statement-facing notation. The flag-realization and central
conditions below are conclusions of TateComparison, not fields or hypotheses of its
input data. Every lattice comparison uses actual isogeny Tate maps, and
the central condition concerns the universal family and its marking.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct Pointwise

section

def Local.IntegralType.central (s : ℕ) : Local.IntegralType s := ⟨Local.LocalType.central s, Local.LocalType.central_integral s⟩

end

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)

/-- An integral split frame respects the actual O_E action on Tate modules
and identifies the source integral lattice with its independent blocks. -/
def Data.SphericalPELAlbaneseData.IsIntegralSplitFrame {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)
    (e : D.FiberFrame b x)
    (B : Fin s → LinearMap.BilinForm ℚ_[q] (Fin 3 → ℚ_[q]))
    (L₀ : Fin s → Duality.RankThreeLattice ℤ_[q] ℚ_[q]) : Prop :=
  Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q
    D.localCharacter e ∧
    Rational.framedIntegralTateImage e =
        Submodule.pi Set.univ (fun v : Fin s × Bool =>
          if v.2 then (B v.1).dualSubmodule (L₀ v.1).val else (L₀ v.1).val)

/-- The geometric flag assertion, expressed intrinsically: a single split
source frame identifies actual isogeny Tate lattices with ordinary flags.
The same composite isogeny supplies both the polarized marking and the
linear realization, and it depends only on the terminal chosen lattices. -/
def Data.SphericalPELAlbaneseData.HasPolarizedFlagRealizations (hIsogenyQuotient : D.RealizesIsogenyQuotient) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b),
    ∃ (e : D.FiberFrame b x)
      (B : Fin s → LinearMap.BilinForm ℚ_[q] (Fin 3 → ℚ_[q]))
      (L₀ : Fin s → Duality.RankThreeLattice ℤ_[q] ℚ_[q]),
      (∀ v, (B v).Nondegenerate) ∧ D.IsIntegralSplitFrame b x e B L₀ ∧
      ∀ ts : List (Local.IntegralType s),
        ∃ (flags : D.PELFlag b x ts ≃ Duality.LinearBlockFlags (q : ℤ_[q]) L₀ ts)
          (composite : Duality.LinearBlockFlags (q : ℤ_[q]) L₀ ts → D.CompositeDatum x ts),
          (∀ F, D.RealizesLinearFlag hIsogenyQuotient e B L₀ F (flags F) (composite (flags F))) ∧
          ∀ L L', L.val (Fin.last ts.length) = L'.val (Fin.last ts.length) →
            composite L = composite L'

/-- Multiplication by q is asserted on the universal abelian isogeny,
after identifying its target with the correctly shifted marking. -/
def Data.SphericalPELAlbaneseData.CentralIsMultiplicationByQ (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hqN : Nat.Coprime q D.level) : Prop :=
  ∃ e : PELModuli.PELFamilyIso
      ((D.sourceFamily (Local.IntegralType.central s)).shiftMarking (ZMod.unitOfCoprime q hqN))
      (D.targetFamily (Local.IntegralType.central s)),
    (D.c46Isogeny hIsogenyQuotient (Local.IntegralType.central s)).isogeny.hom =
      ((𝟙 (D.sourceFamily (Local.IntegralType.central s)).abelian.scheme) ^ q) ≫ e.abelian.hom ∧
    (D.c46Isogeny hIsogenyQuotient (Local.IntegralType.central s)).dualHom =
      e.dual.inv ≫ ((𝟙 (D.sourceFamily (Local.IntegralType.central s)).dual.abelian.scheme) ^ q)

/-- The central correspondence is the actual graph of the marking automorphism. -/
def Data.SphericalPELAlbaneseData.IsCentralGraph (shift : D.space ≅ D.space) : Prop :=
  ∃ e : (D.correspondence (Local.IntegralType.central s)).cover ≅ D.space,
    e.hom = (D.correspondence (Local.IntegralType.central s)).source ∧
      (D.correspondence (Local.IntegralType.central s)).target = e.hom ≫ shift.hom

abbrev Data.SphericalPELAlbaneseData.componentGeneric (j : Fin D.componentCount) :=
  (Over.pullback D.generic).obj (D.components.S j)

abbrev Data.SphericalPELAlbaneseData.componentInclusion (j : Fin D.componentCount) :=
  (Over.pullback D.generic).map (D.inclusion j)

def Data.SphericalPELAlbaneseData.aTotalPoint (h : D.HasIntegralModelGeometry) {T : Over (Spec (.of K))} (x : T ⟶ D.space) :
    Additive (T ⟶ D.albaneseGroup.X) := Additive.ofMul (x ≫ D.albaneseMap h)

def Data.SphericalPELAlbaneseData.aPoint (h : D.HasIntegralModelGeometry) (j : Fin D.componentCount)
    {T : Over (Spec (.of K))} (x : T ⟶ D.componentGeneric j) :
    Additive (T ⟶ D.albaneseGroup.X) := D.aTotalPoint h (x ≫ D.componentInclusion j)

def Data.SphericalPELAlbaneseData.endPoint (a : D.EndK) {T : Over (Spec (.of K))}
    (x : Additive (T ⟶ D.albaneseGroup.X)) : Additive (T ⟶ D.albaneseGroup.X) :=
  Additive.ofMul (x.toMul ≫ End.endSchemeMap D.albaneseGroup.X a)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
