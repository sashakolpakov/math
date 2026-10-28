import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockTower
import OAI.AlgebraicGeometry.PELModuli.CMPoints.FiniteGroupPresentation
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockSchemeTower

/-! # Block Divisibility -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockDivisibility

noncomputable section

/-! Assemble FiniteEtale's actual q-divisible group from finite affine block
presentations and their geometric ranks. The transition maps and kernel
condition are constructed, rather than included among the rank hypotheses.

Only the actual block functor and its represented closed inclusions are used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {k E K : Type} [Field k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (τ : Gal(E/ℚ))

def finiteBlockPointIso (n : ℕ) (H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k)
    (e : H.scheme ≅ (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X)
    [IsMonHom e.hom] :
    H.points ⋙ forget₂ CommGrpCat GrpCat ≅ BlocksProjectors.affineBlockFunctor A ρ (j.localCharacter iota τ) n :=
  NatIso.ofComponents (fun R =>
    ((CategoryTheory.Hom.mulEquivCongrRight e (GroupSchemes.FiniteEtale.affine k R)).trans
      (((BlockSchemeTower.blockYonedaIso j iota hsplit A ρ n τ).app
        (op (GroupSchemes.FiniteEtale.affine k R))).groupIsoToMulEquiv)).toGrpIso) (by
    intro R S f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change (((algSpec (.of k)).map f.op ≫ x) ≫ e.hom) ≫
      BlockSchemeTower.blockSchemeInclusion j iota hsplit A ρ n τ =
        (algSpec (.of k)).map f.op ≫ ((x ≫ e.hom) ≫ BlockSchemeTower.blockSchemeInclusion j iota hsplit A ρ n τ)
    exact (congrArg (fun z => z ≫ BlockSchemeTower.blockSchemeInclusion j iota hsplit A ρ n τ)
      (Category.assoc ((algSpec (.of k)).map f.op) x e.hom)).trans
        (Category.assoc _ _ _))

theorem finiteBlockPointIso_val (n : ℕ) (H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k)
    (e : H.scheme ≅ (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X)
    [IsMonHom e.hom] (R : CommAlgCat k) (x : GroupSchemes.FiniteEtale.affine k R ⟶ H.scheme) :
    ((finiteBlockPointIso j iota hsplit A ρ τ n H e).hom.app R x).val =
      (x ≫ e.hom) ≫ BlockSchemeTower.blockSchemeInclusion j iota hsplit A ρ n τ := rfl

variable (H : ℕ → GroupSchemes.FiniteEtale.FiniteCommGroupScheme k)
  (e : ∀ n, (H n).scheme ≅ (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X)
  [∀ n, IsMonHom (e n).hom]

def affineBlockTransition (n : ℕ) : (H n).scheme ⟶ (H (n + 1)).scheme :=
  (e n).hom ≫
    (BlockSchemeTower.blockSchemeLevelEmbedding j iota hsplit A ρ τ (Nat.le_succ n)).hom.hom ≫ (e (n + 1)).inv

instance affineBlockTransition_group (n : ℕ) :
    IsMonHom (affineBlockTransition j iota hsplit A ρ τ H e n) := by
  dsimp only [affineBlockTransition]
  infer_instance

instance affineBlockTransition_closed (n : ℕ) :
    IsClosedImmersion (affineBlockTransition j iota hsplit A ρ τ H e n).left := by
  have : IsIso (e n).hom.left := inferInstanceAs
    (IsIso (((Over.forget (Spec (.of k))).mapIso (e n)).hom))
  have : IsIso (e (n + 1)).inv.left := inferInstanceAs
    (IsIso (((Over.forget (Spec (.of k))).mapIso (e (n + 1))).inv))
  dsimp only [affineBlockTransition, Over.comp_left]
  infer_instance

theorem affineBlockTransition_points (n : ℕ) (R : CommAlgCat k)
    (x : GroupSchemes.FiniteEtale.affine k R ⟶ (H n).scheme) :
    ((finiteBlockPointIso j iota hsplit A ρ τ (n + 1) (H (n + 1)) (e (n + 1))).hom.app R
      (x ≫ affineBlockTransition j iota hsplit A ρ τ H e n)).val =
        ((finiteBlockPointIso j iota hsplit A ρ τ n (H n) (e n)).hom.app R x).val := by
  simp only [finiteBlockPointIso_val, affineBlockTransition, Category.assoc,
    Iso.inv_hom_id_assoc, BlockSchemeTower.blockSchemeLevelEmbedding_inclusion]

theorem affineBlockTransition_kernel (n : ℕ) (R : CommAlgCat k)
    (x : GroupSchemes.FiniteEtale.affine k R ⟶ (H (n + 1)).scheme) :
    (∃ y, y ≫ affineBlockTransition j iota hsplit A ρ τ H e n = x) ↔ x ^ (q ^ n) = 1 := by
  let en : (GroupSchemes.FiniteEtale.affine k R ⟶ (H n).scheme) ≃*
      BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n (GroupSchemes.FiniteEtale.affine k R) :=
    ((finiteBlockPointIso j iota hsplit A ρ τ n (H n) (e n)).app R).groupIsoToMulEquiv
  let enext : (GroupSchemes.FiniteEtale.affine k R ⟶ (H (n + 1)).scheme) ≃*
      BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) (n + 1) (GroupSchemes.FiniteEtale.affine k R) :=
    ((finiteBlockPointIso j iota hsplit A ρ τ (n + 1) (H (n + 1)) (e (n + 1))).app R).groupIsoToMulEquiv
  let transition := IsMonHom.monoidHom
    (affineBlockTransition j iota hsplit A ρ τ H e n) (GroupSchemes.FiniteEtale.affine k R)
  exact BlockTower.torsion_kernel_transport en enext transition
    (BlockTower.blockLevelInclusion A ρ (j.localCharacter iota τ) n (n + 1) (Nat.le_succ n)
      (GroupSchemes.FiniteEtale.affine k R)) (q ^ n)
    (fun y => Subtype.ext (affineBlockTransition_points j iota hsplit A ρ τ H e n R y))
    (BlockTower.blockLevelInclusion_kernel A ρ (j.localCharacter iota τ) n (n + 1) (Nat.le_succ n)
      (GroupSchemes.FiniteEtale.affine k R)) x

def blockDivisibleGroupOfRanks (h : ℕ)
    (hrank : ∀ n, Module.finrank k (H n).algebra = q ^ (n * h)) :
    GroupSchemes.FiniteEtale.PDivisibleGroup k q h where
  level := H
  inclusion := affineBlockTransition j iota hsplit A ρ τ H e
  inclusion_hom := affineBlockTransition_group j iota hsplit A ρ τ H e
  inclusion_closed := affineBlockTransition_closed j iota hsplit A ρ τ H e
  rank := hrank
  kernel := affineBlockTransition_kernel j iota hsplit A ρ τ H e

include hsplit e in
/-- The geometric ranks are the remaining numerical input to this
construction of the actual q-divisible block. -/
theorem blockHasHeight_of_finite_presentations (h : ℕ)
    (hrank : ∀ n, Module.finrank k (H n).algebra = q ^ (n * h)) :
    BlocksProjectors.BlockHasHeight A ρ (j.localCharacter iota τ) h := by
  refine ⟨blockDivisibleGroupOfRanks j iota hsplit A ρ τ H e h hrank,
    fun n => finiteBlockPointIso j iota hsplit A ρ τ n (H n) (e n), ?_⟩
  exact affineBlockTransition_points j iota hsplit A ρ τ H e

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockDivisibility
