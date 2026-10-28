import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CoefficientPerfection
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierNondegeneracy

/-! # Nondegeneracy -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.Nondegeneracy

noncomputable section

/-! The actual canonical coefficient pairing has trivial annihilator
of the whole block. This follows directly from its sheaf adjoint being
an isomorphism, on every scheme-valued point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CoefficientPerfection OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierNondegeneracy

theorem sheaf_character_eq_one_of_values {S : Scheme.{u}} (G : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) (T : Over S)
    (χ : (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G).obj.obj (.op T))
    (h : ∀ (U : Over S) (t : U ⟶ T) (a : G.obj.obj (.op U)),
      AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G U ((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G).obj.map t.op χ) a = 1) : χ = 1 := by
  apply NatTrans.ext
  funext V
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro a
  exact (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue_restrict G T χ V.unop a).symm.trans
    (h V.unop.left V.unop.hom a)

theorem perfect_pairing_annihilator_whole {S : Scheme.{u}} {A B P : Over S}
    [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (he : e.toSheafPairing.IsPerfect) :
    e.relativeAnnihilator (CompactOpposites.Kernel.wholeRelativeSubgroup A P) = AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := B) (P := P) := by
  ext T t b
  constructor
  · intro hb
    let d := e.toSheafPairing.rightAdjoint
    have : IsIso d := he.2
    have hm : Mono (d.hom.app (.op T)) := inferInstance
    have hc : d.hom.app (.op T) (ULift.up b) = 1 := by
      apply sheaf_character_eq_one_of_values
      intro U f a
      obtain ⟨a⟩ := a
      have hn := d.hom.naturality_apply f.op (ULift.up b)
      exact (congrArg (fun χ => AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) U χ (ULift.up a))
        hn.symm).trans ((e.toSheafPairing_rightValue U a (f ≫ b)).trans
          (congrArg ULift.up (hb U f a (Subgroup.mem_top a))))
    change b = 1
    have hh := (CommGrpCat.mono_iff_injective (d.hom.app (.op T))).mp hm
      (hc.trans (d.hom.app (.op T)).hom.map_one.symm)
    exact congrArg ULift.down hh
  · intro hb
    change b = 1 at hb
    subst b
    intro U f a _
    change e.pairValue a (f ≫ 1) = 1
    rw [MonObj.comp_one]
    exact e.one_right U a

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

theorem canonical_coefficient_zero_double (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (hdegree : q.Coprime (∏ i, δ i)) (n : ℕ) (τ υ : Gal(E/ℚ))
    (hυ : υ = PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) {P : Over (Spec (.of k))} :
    (CoefficientPerfection.canonicalCoefficientPairing j iota hsplit A ρ n τ υ).relativeAnnihilator
      ((CoefficientPerfection.canonicalCoefficientPairing j iota hsplit A ρ n τ υ).flip.relativeAnnihilator
        (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n υ)))
          (P := P))) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n υ)))
        (P := P) :=
  CartierNondegeneracy.zero_double_annihilator_of_whole _ (perfect_pairing_annihilator_whole _
    (CoefficientPerfection.canonicalCoefficientPairing_isPerfect j iota hsplit A ρ hρ hdegree n τ υ hυ))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.Nondegeneracy
