import OAI.NumberTheory.PadicHodge.IntegralComparison.DisjointCoverModuleProjective
import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleGeometricObjectCovering
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology
import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleDegreeZero
import Mathlib.AlgebraicGeometry.Limits

/-! # Point Coproduct -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.PointCoproduct

noncomputable section

/-! Exact global sections and positive-degree vanishing on an actual disjoint union of geometric points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (ι : Type u) (K : ι → Type u) [∀ i, Field (K i)]

local notation "Y" => (fun i => Spec (CommRingCat.of (K i)))
local notation "X" => (∐ Y)

def object (i : ι) : (X).ProEt := Scheme.ProEt.mk (Sigma.ι Y i)

def hom (i : ι) : object ι K i ⟶ Scheme.ProEt.mk (𝟙 X) :=
  MorphismProperty.Over.homMk (Sigma.ι Y i) (Category.comp_id _)

instance mono (i : ι) : Mono (hom ι K i) :=
  (Scheme.ProEt.forget X ⋙ Over.forget X).mono_of_mono_map
    (inferInstanceAs (Mono (Sigma.ι Y i)))

theorem cover : Sieve.ofArrows (object ι K) (hom ι K) ∈ Scheme.ProEt.topology X (Scheme.ProEt.mk (𝟙 X)) := by
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.ofArrows (object ι K) (hom ι K)).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
    Scheme.proetalePrecoverage X
  rw [Presieve.map_ofArrows]
  change Presieve.ofArrows Y (Sigma.ι Y) ∈ Scheme.proetalePrecoverage X
  apply Scheme.etalePrecoverage_le_proetalePrecoverage
  apply (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr
  exact ⟨fun x => (sigmaOpenCover Y).exists_eq x, fun i => inferInstanceAs (Etale (Sigma.ι Y i))⟩

theorem disjoint {W : (X).ProEt} {i j : ι} (hij : i ≠ j)
    (a : W ⟶ object ι K i) (b : W ⟶ object ι K j)
    (h : a ≫ hom ι K i = b ≫ hom ι K j) : (⊥ : Sieve W) ∈ Scheme.ProEt.topology X W := by
  have he : a.left ≫ Sigma.ι Y i = b.left ≫ Sigma.ι Y j := congrArg
    (fun q : W ⟶ Scheme.ProEt.mk (𝟙 X) => q.left) h
  let : IsEmpty W.left := isEmpty_of_commSq_sigmaι_of_ne ⟨he⟩ hij
  exact Scheme.ProEt.bot_mem_topology W

variable [∀ i, IsAlgClosed (K i)]

theorem split (i : ι) (S : Sieve (object ι K i)) (hS : S ∈ Scheme.ProEt.topology X _) : S = ⊤ :=
  EtaleGeometricObjectCovering.Pro.split (K i) X (Sigma.ι Y i) S hS

variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem projective : Projective (Cohomology.constantUnitSheaf ℓ X) :=
  DisjointCoverModuleProjective.projective (Scheme.ProEt.topology X) (Cohomology.Coeff.{u} ℓ)
    (object ι K) (hom ι K) (cover ι K) (fun {_W} {_i} {_j} hij a b h => disjoint ι K hij a b h)
    (split ι K) (PeriodInvariants.EtaleDegreeZero.identityTerminal X)

theorem vanishing (n : ℕ) : Subsingleton (Cohomology.RationalEllAdicCohomology ℓ X (n + 1)) := by
  let := projective ι K ℓ
  exact Abelian.Ext.subsingleton_of_projective _ _ n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.PointCoproduct
