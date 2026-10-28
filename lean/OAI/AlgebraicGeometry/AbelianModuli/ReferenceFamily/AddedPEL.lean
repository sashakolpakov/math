import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Data

/-! # Added PEL -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AddedPEL

noncomputable section

/-! The added-level PEL problem retains both markings on one polarized
family. Forgetting a marking preserves its action, Rosati condition and
Lie ranks by construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {s N L : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
  {T : Over (Spec (.of K))}

/-- A PEL object at the auxiliary level together with the prescribed
marking on exactly the same abelian scheme. -/
structure AddedPELLevel (P : Datum.RankThreePELDatum E s) (iota : E →+* K)
    (L N : ℕ) (T : Over (Spec (.of K))) where
  auxiliary : PEL.Objects.PELObject P iota L T
  prescribed : auxiliary.polarized.abelian.FullLevel N

namespace AddedPELLevel

def forgetAuxiliary (A : AddedPELLevel P iota L N T) : PEL.Objects.PELObject P iota N T where
  polarized := (Level.Data.AddedFullLevel.mk A.auxiliary.polarized A.prescribed).forgetAuxiliary
  action := A.auxiliary.action
  rosati := A.auxiliary.rosati
  lieRanks := A.auxiliary.lieRanks

/-- Adding an auxiliary marking requires only that marking; it does not
require a new PEL action or a new comparison hypothesis. -/
def ofPrescribed (A : PEL.Objects.PELObject P iota N T) (α : A.polarized.abelian.FullLevel L) :
    AddedPELLevel P iota L N T where
  auxiliary := {
    polarized := {
      abelian := A.polarized.abelian
      dual := A.polarized.dual
      polarization := A.polarized.polarization
      level := α }
    action := A.action
    rosati := A.rosati
    lieRanks := A.lieRanks }
  prescribed := A.polarized.level

@[simp] theorem forget_ofPrescribed (A : PEL.Objects.PELObject P iota N T)
    (α : A.polarized.abelian.FullLevel L) :
    (ofPrescribed A α).forgetAuxiliary = A := rfl

def swap (A : AddedPELLevel P iota L N T) : AddedPELLevel P iota N L T :=
  ofPrescribed A.auxiliary A.prescribed

@[simp] theorem swap_swap (A : AddedPELLevel P iota L N T) : A.swap.swap = A := rfl

/-- The two-level problem can equally be described starting from the
prescribed-level object and choosing its auxiliary full level. -/
def prescribedDescription : AddedPELLevel P iota L N T ≃
    (Σ A : PEL.Objects.PELObject P iota N T, A.polarized.abelian.FullLevel L) where
  toFun A := ⟨A.forgetAuxiliary, A.auxiliary.polarized.level⟩
  invFun A := ofPrescribed A.1 A.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every two choices of auxiliary marking differ by a unique actual
automorphism of the constant level functor. This is the descent relation
on the marking fiber, before proving effectiveness on moduli schemes. -/
theorem unique_auxiliary_change (A : PEL.Objects.PELObject P iota N T)
    (α β : A.polarized.abelian.FullLevel L) :
    ∃! change : HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor (3 * s) L T.left ≅
        HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor (3 * s) L T.left,
      change ≪≫ α = β := Level.Data.existsUnique_change_of_frame α β

end AddedPELLevel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AddedPEL
