import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks

/-! # Objects -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects

noncomputable section

/-! Actual objects and isomorphism classes of the characteristic-zero PEL
problem. The field action, Rosati constraint, and geometric Lie eigenspaces
are stated on the polarized abelian schemes supplied by HilbertConstruction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ}

def HasPrescribedLieRanks (P : Datum.RankThreePELDatum E s) (iota : E →+* K)
    (T : Over (Spec (.of K))) (A : HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (j : K →+* F)
    (p : Spec (.of F) ⟶ T.left),
    p ≫ T.hom = Spec.map (CommRingCat.ofHom j) →
    ∀ τ : E ≃ₐ[ℚ] E,
      LieRanks.HasLieRank (A.pullback p) (ρ.pullback p)
        ((j.comp iota).comp (τ.toRingHom.comp
          (algebraMap (NumberField.RingOfIntegers E) E))) (P.lieRank τ)

/-- A polarized abelian scheme with the integral CM action and the
prescribed ranks. There is no moduli-space or analytic-chart field. -/
structure PELObject (P : Datum.RankThreePELDatum E s) (iota : E →+* K)
    (N : ℕ) (T : Over (Spec (.of K))) where
  polarized : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N T.left
  action : ActionData.IntegralAction (NumberField.RingOfIntegers E) polarized.abelian
  rosati : ActionData.RosatiConjugation polarized action
  lieRanks : HasPrescribedLieRanks P iota T polarized.abelian action

variable {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
  {T : Over (Spec (.of K))}

structure PELIso (A B : PELObject P iota N T) where
  polarized : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A.polarized B.polarized
  action : ∀ a : NumberField.RingOfIntegers E,
    A.action.map a ≫ polarized.abelian.hom = polarized.abelian.hom ≫ B.action.map a

namespace PELIso

variable {A B C : PELObject P iota N T}

def refl (A : PELObject P iota N T) : PELIso A A where
  polarized := HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.refl A.polarized
  action a := by simp [HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.refl]

def symm (e : PELIso A B) : PELIso B A where
  polarized := e.polarized.symm
  action a := by
    change B.action.map a ≫ e.polarized.abelian.inv =
      e.polarized.abelian.inv ≫ A.action.map a
    apply (cancel_epi e.polarized.abelian.hom).mp
    rw [← Category.assoc, ← e.action a]
    simp

def trans (e : PELIso A B) (f : PELIso B C) : PELIso A C where
  polarized := e.polarized.trans f.polarized
  action a := by
    change A.action.map a ≫ (e.polarized.abelian.hom ≫ f.polarized.abelian.hom) =
      (e.polarized.abelian.hom ≫ f.polarized.abelian.hom) ≫ C.action.map a
    rw [← Category.assoc, e.action a, Category.assoc, f.action a, Category.assoc]

end PELIso

def pelSetoid (P : Datum.RankThreePELDatum E s) (iota : E →+* K)
    (N : ℕ) (T : Over (Spec (.of K))) : Setoid (PELObject P iota N T) where
  r A B := Nonempty (PELIso A B)
  iseqv := {
    refl A := ⟨PELIso.refl A⟩
    symm := fun ⟨e⟩ => ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

def PELClasses (P : Datum.RankThreePELDatum E s) (iota : E →+* K)
    (N : ℕ) (T : Over (Spec (.of K))) := Quotient (pelSetoid P iota N T)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects
